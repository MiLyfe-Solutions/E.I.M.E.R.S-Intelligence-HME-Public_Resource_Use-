import V185TrunkScan23Chunk1368

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8107566 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_8107566 : Nat := 118140960795 + 8107566 * 2 ^ 59
def prefixEnd_8107566 : Nat := 4983230072969 + 3 ^ 40 * 8107566 * 2
def baseEnd_8107566 : Nat := 4163078296050331344438989

theorem tailTrace_8107566 : CollatzResearch.WordTrace tailWord_8107566 prefixEnd_8107566 4163078296050331344438989 := by
  unfold tailWord_8107566
  simp only [CollatzResearch.WordTrace]
  refine ⟨36963403168210064859916819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197138150230453679252889701 36963403168210064859916819)
  ·
    refine ⟨55445104752315097289875229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36963403168210064859916819 55445104752315097289875229)
    ·
      refine ⟨20791914282118161483703211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55445104752315097289875229 20791914282118161483703211)
      ·
        refine ⟨31187871423177242225554817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20791914282118161483703211 31187871423177242225554817)
        ·
          refine ⟨23390903567382931669166113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31187871423177242225554817 23390903567382931669166113)
          ·
            refine ⟨17543177675537198751874585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23390903567382931669166113 17543177675537198751874585)
            ·
              refine ⟨13157383256652899063905939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17543177675537198751874585 13157383256652899063905939)
              ·
                refine ⟨19736074884979348595858909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157383256652899063905939 19736074884979348595858909)
                ·
                  refine ⟨7401028081867255723447091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19736074884979348595858909 7401028081867255723447091)
                  ·
                    refine ⟨11101542122800883585170637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401028081867255723447091 11101542122800883585170637)
                    ·
                      refine ⟨4163078296050331344438989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11101542122800883585170637 4163078296050331344438989)
                      ·
                        rfl

theorem cell23_8107566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_8107566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107566 prefixEnd_8107566 := by exact prefixLift 8107566
  have htrace : WordTrace (prefixWord ++ tailWord_8107566) baseStart_8107566 baseEnd_8107566 := by
    simpa [prefixWord, tailWord_8107566, baseEnd_8107566] using wordTrace_append hprefix tailTrace_8107566
  have hstable : (prefixWord ++ tailWord_8107566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107566).length < 2 ^ (prefixWord ++ tailWord_8107566).sum := by decide
  have hdescent : baseEnd_8107566 < baseStart_8107566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107575 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_8107575 : Nat := 118140960795 + 8107575 * 2 ^ 59
def prefixEnd_8107575 : Nat := 4983230072969 + 3 ^ 40 * 8107575 * 2
def baseEnd_8107575 : Nat := 4163082917376221809226447

theorem tailTrace_8107575 : CollatzResearch.WordTrace tailWord_8107575 prefixEnd_8107575 4163082917376221809226447 := by
  unfold tailWord_8107575
  simp only [CollatzResearch.WordTrace]
  refine ⟨295707553602647913416412179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197138369068431942277608119 295707553602647913416412179)
  ·
    refine ⟨443561330403971870124618269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295707553602647913416412179 443561330403971870124618269)
    ·
      refine ⟨166335498901489451296731851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443561330403971870124618269 166335498901489451296731851)
      ·
        refine ⟨249503248352234176945097777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166335498901489451296731851 249503248352234176945097777)
        ·
          refine ⟨187127436264175632708823333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249503248352234176945097777 187127436264175632708823333)
          ·
            refine ⟨35086394299532931132904375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187127436264175632708823333 35086394299532931132904375)
            ·
              refine ⟨52629591449299396699356563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35086394299532931132904375 52629591449299396699356563)
              ·
                refine ⟨78944387173949095049034845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52629591449299396699356563 78944387173949095049034845)
                ·
                  refine ⟨29604145190230910643388067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78944387173949095049034845 29604145190230910643388067)
                  ·
                    refine ⟨44406217785346365965082101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29604145190230910643388067 44406217785346365965082101)
                    ·
                      refine ⟨4163082917376221809226447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44406217785346365965082101 4163082917376221809226447)
                      ·
                        rfl

theorem cell23_8107575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_8107575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107575 prefixEnd_8107575 := by exact prefixLift 8107575
  have htrace : WordTrace (prefixWord ++ tailWord_8107575) baseStart_8107575 baseEnd_8107575 := by
    simpa [prefixWord, tailWord_8107575, baseEnd_8107575] using wordTrace_append hprefix tailTrace_8107575
  have hstable : (prefixWord ++ tailWord_8107575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107575).length < 2 ^ (prefixWord ++ tailWord_8107575).sum := by decide
  have hdescent : baseEnd_8107575 < baseStart_8107575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107589 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_8107589 : Nat := 118140960795 + 8107589 * 2 ^ 59
def prefixEnd_8107589 : Nat := 4983230072969 + 3 ^ 40 * 8107589 * 2
def baseEnd_8107589 : Nat := 4163090106105384754451383

theorem tailTrace_8107589 : CollatzResearch.WordTrace tailWord_8107589 prefixEnd_8107589 4163090106105384754451383 := by
  unfold tailWord_8107589
  simp only [CollatzResearch.WordTrace]
  refine ⟨295708064224597193807421821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197138709483064795871614547 295708064224597193807421821)
  ·
    refine ⟨110890524084223947677783183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295708064224597193807421821 110890524084223947677783183)
    ·
      refine ⟨166335786126335921516674775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110890524084223947677783183 166335786126335921516674775)
      ·
        refine ⟨249503679189503882275012163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166335786126335921516674775 249503679189503882275012163)
        ·
          refine ⟨374255518784255823412518245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249503679189503882275012163 374255518784255823412518245)
          ·
            refine ⟨70172909772047966889847171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374255518784255823412518245 70172909772047966889847171)
            ·
              refine ⟨105259364658071950334770757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70172909772047966889847171 105259364658071950334770757)
              ·
                refine ⟨19736130873388490687769517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105259364658071950334770757 19736130873388490687769517)
                ·
                  refine ⟨7401049077520684007913569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19736130873388490687769517 7401049077520684007913569)
                  ·
                    refine ⟨5550786808140513005935177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401049077520684007913569 5550786808140513005935177)
                    ·
                      refine ⟨4163090106105384754451383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550786808140513005935177 4163090106105384754451383)
                      ·
                        rfl

theorem cell23_8107589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_8107589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107589 prefixEnd_8107589 := by exact prefixLift 8107589
  have htrace : WordTrace (prefixWord ++ tailWord_8107589) baseStart_8107589 baseEnd_8107589 := by
    simpa [prefixWord, tailWord_8107589, baseEnd_8107589] using wordTrace_append hprefix tailTrace_8107589
  have hstable : (prefixWord ++ tailWord_8107589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107589).length < 2 ^ (prefixWord ++ tailWord_8107589).sum := by decide
  have hdescent : baseEnd_8107589 < baseStart_8107589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107612 : List Nat := [2, 2, 4, 1, 2, 3, 9]
def baseStart_8107612 : Nat := 118140960795 + 8107612 * 2 ^ 59
def prefixEnd_8107612 : Nat := 4983230072969 + 3 ^ 40 * 8107612 * 2
def baseEnd_8107612 : Nat := 51396319952598002030417

theorem tailTrace_8107612 : CollatzResearch.WordTrace tailWord_8107612 prefixEnd_8107612 51396319952598002030417 := by
  unfold tailWord_8107612
  simp only [CollatzResearch.WordTrace]
  refine ⟨147854451551756934367754545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197139268735675912490339393 147854451551756934367754545)
  ·
    refine ⟨110890838663817700775815909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147854451551756934367754545 110890838663817700775815909)
    ·
      refine ⟨20792032249465818895465483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110890838663817700775815909 20792032249465818895465483)
      ·
        refine ⟨31188048374198728343198225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792032249465818895465483 31188048374198728343198225)
        ·
          refine ⟨23391036280649046257398669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31188048374198728343198225 23391036280649046257398669)
          ·
            refine ⟨8771638605243392346524501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23391036280649046257398669 8771638605243392346524501)
            ·
              refine ⟨51396319952598002030417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8771638605243392346524501 51396319952598002030417)
              ·
                rfl

theorem cell23_8107612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 9].length) (baseStart_8107612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107612 prefixEnd_8107612 := by exact prefixLift 8107612
  have htrace : WordTrace (prefixWord ++ tailWord_8107612) baseStart_8107612 baseEnd_8107612 := by
    simpa [prefixWord, tailWord_8107612, baseEnd_8107612] using wordTrace_append hprefix tailTrace_8107612
  have hstable : (prefixWord ++ tailWord_8107612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107612).length < 2 ^ (prefixWord ++ tailWord_8107612).sum := by decide
  have hdescent : baseEnd_8107612 < baseStart_8107612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107656 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_8107656 : Nat := 118140960795 + 8107656 * 2 ^ 59
def prefixEnd_8107656 : Nat := 4983230072969 + 3 ^ 40 * 8107656 * 2
def baseEnd_8107656 : Nat := 4163124509309235992313575

theorem tailTrace_8107656 : CollatzResearch.WordTrace tailWord_8107656 prefixEnd_8107656 4163124509309235992313575 := by
  unfold tailWord_8107656
  simp only [CollatzResearch.WordTrace]
  refine ⟨147855253957677232125055411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197140338610236309500073881 147855253957677232125055411)
  ·
    refine ⟨221782880936515848187583117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147855253957677232125055411 221782880936515848187583117)
    ·
      refine ⟨83168580351193443070343669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221782880936515848187583117 83168580351193443070343669)
      ·
        refine ⟨7797054407924385287844719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83168580351193443070343669 7797054407924385287844719)
        ·
          refine ⟨11695581611886577931767079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797054407924385287844719 11695581611886577931767079)
          ·
            refine ⟨17543372417829866897650619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695581611886577931767079 17543372417829866897650619)
            ·
              refine ⟨26315058626744800346475929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17543372417829866897650619 26315058626744800346475929)
              ·
                refine ⟨19736293970058600259856947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26315058626744800346475929 19736293970058600259856947)
                ·
                  refine ⟨29604440955087900389785421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19736293970058600259856947 29604440955087900389785421)
                  ·
                    refine ⟨11101665358157962646169533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29604440955087900389785421 11101665358157962646169533)
                    ·
                      refine ⟨4163124509309235992313575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11101665358157962646169533 4163124509309235992313575)
                      ·
                        rfl

theorem cell23_8107656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_8107656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107656 prefixEnd_8107656 := by exact prefixLift 8107656
  have htrace : WordTrace (prefixWord ++ tailWord_8107656) baseStart_8107656 baseEnd_8107656 := by
    simpa [prefixWord, tailWord_8107656, baseEnd_8107656] using wordTrace_append hprefix tailTrace_8107656
  have hstable : (prefixWord ++ tailWord_8107656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107656).length < 2 ^ (prefixWord ++ tailWord_8107656).sum := by decide
  have hdescent : baseEnd_8107656 < baseStart_8107656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_8107665 : Nat := 118140960795 + 8107665 * 2 ^ 59
def prefixEnd_8107665 : Nat := 4983230072969 + 3 ^ 40 * 8107665 * 2
def baseEnd_8107665 : Nat := 4163129130635126457101033

theorem tailTrace_8107665 : CollatzResearch.WordTrace tailWord_8107665 prefixEnd_8107665 4163129130635126457101033 := by
  unfold tailWord_8107665
  simp only [CollatzResearch.WordTrace]
  refine ⟨295710836172321858787188449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197140557448214572524792299 295710836172321858787188449)
  ·
    refine ⟨221783127129241394090391337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295710836172321858787188449 221783127129241394090391337)
    ·
      refine ⟨166337345346931045567793503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221783127129241394090391337 166337345346931045567793503)
      ·
        refine ⟨249506018020396568351690255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166337345346931045567793503 249506018020396568351690255)
        ·
          refine ⟨374259027030594852527535383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249506018020396568351690255 374259027030594852527535383)
          ·
            refine ⟨561388540545892278791303075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374259027030594852527535383 561388540545892278791303075)
            ·
              refine ⟨842082810818838418186954613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561388540545892278791303075 842082810818838418186954613)
              ·
                refine ⟨78945263514266101705026995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842082810818838418186954613 78945263514266101705026995)
                ·
                  refine ⟨118417895271399152557540493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78945263514266101705026995 118417895271399152557540493)
                  ·
                    refine ⟨44406710726774682209077685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118417895271399152557540493 44406710726774682209077685)
                    ·
                      refine ⟨4163129130635126457101033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44406710726774682209077685 4163129130635126457101033)
                      ·
                        rfl

theorem cell23_8107665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_8107665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107665 prefixEnd_8107665 := by exact prefixLift 8107665
  have htrace : WordTrace (prefixWord ++ tailWord_8107665) baseStart_8107665 baseEnd_8107665 := by
    simpa [prefixWord, tailWord_8107665, baseEnd_8107665] using wordTrace_append hprefix tailTrace_8107665
  have hstable : (prefixWord ++ tailWord_8107665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107665).length < 2 ^ (prefixWord ++ tailWord_8107665).sum := by decide
  have hdescent : baseEnd_8107665 < baseStart_8107665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107696 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2]
def baseStart_8107696 : Nat := 118140960795 + 8107696 * 2 ^ 59
def prefixEnd_8107696 : Nat := 4983230072969 + 3 ^ 40 * 8107696 * 2
def baseEnd_8107696 : Nat := 4163145048535415835813391

theorem tailTrace_8107696 : CollatzResearch.WordTrace tailWord_8107696 prefixEnd_8107696 4163145048535415835813391 := by
  unfold tailWord_8107696
  simp only [CollatzResearch.WordTrace]
  refine ⟨147855983417604775540783471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197141311223473034054377961 147855983417604775540783471)
  ·
    refine ⟨221783975126407163311175207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147855983417604775540783471 221783975126407163311175207)
    ·
      refine ⟨332675962689610744966762811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221783975126407163311175207 332675962689610744966762811)
      ·
        refine ⟨499013944034416117450144217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332675962689610744966762811 499013944034416117450144217)
        ·
          refine ⟨374260458025812088087608163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499013944034416117450144217 374260458025812088087608163)
          ·
            refine ⟨561390687038718132131412245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374260458025812088087608163 561390687038718132131412245)
            ·
              refine ⟨26315188454939912443659949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561390687038718132131412245 26315188454939912443659949)
              ·
                refine ⟨9868195670602467166372481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26315188454939912443659949 9868195670602467166372481)
                ·
                  refine ⟨7401146752951850374779361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868195670602467166372481 7401146752951850374779361)
                  ·
                    refine ⟨5550860064713887781084521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401146752951850374779361 5550860064713887781084521)
                    ·
                      refine ⟨4163145048535415835813391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550860064713887781084521 4163145048535415835813391)
                      ·
                        rfl

theorem cell23_8107696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2].length) (baseStart_8107696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107696 prefixEnd_8107696 := by exact prefixLift 8107696
  have htrace : WordTrace (prefixWord ++ tailWord_8107696) baseStart_8107696 baseEnd_8107696 := by
    simpa [prefixWord, tailWord_8107696, baseEnd_8107696] using wordTrace_append hprefix tailTrace_8107696
  have hstable : (prefixWord ++ tailWord_8107696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107696).length < 2 ^ (prefixWord ++ tailWord_8107696).sum := by decide
  have hdescent : baseEnd_8107696 < baseStart_8107696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107712 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_8107712 : Nat := 118140960795 + 8107712 * 2 ^ 59
def prefixEnd_8107712 : Nat := 4983230072969 + 3 ^ 40 * 8107712 * 2
def baseEnd_8107712 : Nat := 4163153264225887773213317

theorem tailTrace_8107712 : CollatzResearch.WordTrace tailWord_8107712 prefixEnd_8107712 4163153264225887773213317 := by
  unfold tailWord_8107712
  simp only [CollatzResearch.WordTrace]
  refine ⟨147856275201575792907074695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197141700268767723876099593 147856275201575792907074695)
  ·
    refine ⟨221784412802363689360612043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147856275201575792907074695 221784412802363689360612043)
    ·
      refine ⟨332676619203545534040918065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221784412802363689360612043 332676619203545534040918065)
      ·
        refine ⟨249507464402659150530688549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332676619203545534040918065 249507464402659150530688549)
        ·
          refine ⟨46782649575498590724504103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249507464402659150530688549 46782649575498590724504103)
          ·
            refine ⟨70173974363247886086756155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46782649575498590724504103 70173974363247886086756155)
            ·
              refine ⟨105260961544871829130134233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70173974363247886086756155 105260961544871829130134233)
              ·
                refine ⟨78945721158653871847600675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105260961544871829130134233 78945721158653871847600675)
                ·
                  refine ⟨118418581737980807771401013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78945721158653871847600675 118418581737980807771401013)
                  ·
                    refine ⟨11101742037935700728568845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118418581737980807771401013 11101742037935700728568845)
                    ·
                      refine ⟨4163153264225887773213317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11101742037935700728568845 4163153264225887773213317)
                      ·
                        rfl

theorem cell23_8107712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_8107712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107712 prefixEnd_8107712 := by exact prefixLift 8107712
  have htrace : WordTrace (prefixWord ++ tailWord_8107712) baseStart_8107712 baseEnd_8107712 := by
    simpa [prefixWord, tailWord_8107712, baseEnd_8107712] using wordTrace_append hprefix tailTrace_8107712
  have hstable : (prefixWord ++ tailWord_8107712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107712).length < 2 ^ (prefixWord ++ tailWord_8107712).sum := by decide
  have hdescent : baseEnd_8107712 < baseStart_8107712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107719 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 5]
def baseStart_8107719 : Nat := 118140960795 + 8107719 * 2 ^ 59
def prefixEnd_8107719 : Nat := 4983230072969 + 3 ^ 40 * 8107719 * 2
def baseEnd_8107719 : Nat := 462572984287829916202865

theorem tailTrace_8107719 : CollatzResearch.WordTrace tailWord_8107719 prefixEnd_8107719 462572984287829916202865 := by
  unfold tailWord_8107719
  simp only [CollatzResearch.WordTrace]
  refine ⟨295712805714126226009654211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197141870476084150673102807 295712805714126226009654211)
  ·
    refine ⟨443569208571189339014481317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295712805714126226009654211 443569208571189339014481317)
    ·
      refine ⟨83169226607098001065215247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443569208571189339014481317 83169226607098001065215247)
      ·
        refine ⟨124753839910647001597822871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83169226607098001065215247 124753839910647001597822871)
        ·
          refine ⟨187130759865970502396734307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124753839910647001597822871 187130759865970502396734307)
          ·
            refine ⟨280696139798955753595101461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187130759865970502396734307 280696139798955753595101461)
            ·
              refine ⟨13157631553076050949770381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 280696139798955753595101461 13157631553076050949770381)
              ·
                refine ⟨4934111832403519106163893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13157631553076050949770381 4934111832403519106163893)
                ·
                  refine ⟨462572984287829916202865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934111832403519106163893 462572984287829916202865)
                  ·
                    rfl

theorem cell23_8107719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 5].length) (baseStart_8107719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107719 prefixEnd_8107719 := by exact prefixLift 8107719
  have htrace : WordTrace (prefixWord ++ tailWord_8107719) baseStart_8107719 baseEnd_8107719 := by
    simpa [prefixWord, tailWord_8107719, baseEnd_8107719] using wordTrace_append hprefix tailTrace_8107719
  have hstable : (prefixWord ++ tailWord_8107719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107719).length < 2 ^ (prefixWord ++ tailWord_8107719).sum := by decide
  have hdescent : baseEnd_8107719 < baseStart_8107719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107730 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_8107730 : Nat := 118140960795 + 8107730 * 2 ^ 59
def prefixEnd_8107730 : Nat := 4983230072969 + 3 ^ 40 * 8107730 * 2
def baseEnd_8107730 : Nat := 4163162506877668702788235

theorem tailTrace_8107730 : CollatzResearch.WordTrace tailWord_8107730 prefixEnd_8107730 4163162506877668702788235 := by
  unfold tailWord_8107730
  simp only [CollatzResearch.WordTrace]
  refine ⟨73928301729271593722076161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197142137944724249925536429 73928301729271593722076161)
  ·
    refine ⟨55446226296953695291557121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73928301729271593722076161 55446226296953695291557121)
    ·
      refine ⟨41584669722715271468667841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55446226296953695291557121 41584669722715271468667841)
      ·
        refine ⟨31188502292036453601500881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41584669722715271468667841 31188502292036453601500881)
        ·
          refine ⟨23391376719027340201125661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31188502292036453601500881 23391376719027340201125661)
          ·
            refine ⟨8771766269635252575422123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23391376719027340201125661 8771766269635252575422123)
            ·
              refine ⟨13157649404452878863133185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771766269635252575422123 13157649404452878863133185)
              ·
                refine ⟨9868237053339659147349889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13157649404452878863133185 9868237053339659147349889)
                ·
                  refine ⟨7401177790004744360512417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868237053339659147349889 7401177790004744360512417)
                  ·
                    refine ⟨5550883342503558270384313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401177790004744360512417 5550883342503558270384313)
                    ·
                      refine ⟨4163162506877668702788235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550883342503558270384313 4163162506877668702788235)
                      ·
                        rfl

theorem cell23_8107730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_8107730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107730 prefixEnd_8107730 := by exact prefixLift 8107730
  have htrace : WordTrace (prefixWord ++ tailWord_8107730) baseStart_8107730 baseEnd_8107730 := by
    simpa [prefixWord, tailWord_8107730, baseEnd_8107730] using wordTrace_append hprefix tailTrace_8107730
  have hstable : (prefixWord ++ tailWord_8107730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107730).length < 2 ^ (prefixWord ++ tailWord_8107730).sum := by decide
  have hdescent : baseEnd_8107730 < baseStart_8107730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107762 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_8107762 : Nat := 118140960795 + 8107762 * 2 ^ 59
def prefixEnd_8107762 : Nat := 4983230072969 + 3 ^ 40 * 8107762 * 2
def baseEnd_8107762 : Nat := 1387726312752870859196029

theorem tailTrace_8107762 : CollatzResearch.WordTrace tailWord_8107762 prefixEnd_8107762 1387726312752870859196029 := by
  unfold tailWord_8107762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73928593513242611088367385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197142916035313629568979693 73928593513242611088367385)
  ·
    refine ⟨55446445134931958316275539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73928593513242611088367385 55446445134931958316275539)
    ·
      refine ⟨83169667702397937474413309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55446445134931958316275539 83169667702397937474413309)
      ·
        refine ⟨31188625388399226552904991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83169667702397937474413309 31188625388399226552904991)
        ·
          refine ⟨46782938082598839829357487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31188625388399226552904991 46782938082598839829357487)
          ·
            refine ⟨70174407123898259744036231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46782938082598839829357487 70174407123898259744036231)
            ·
              refine ⟨105261610685847389616054347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70174407123898259744036231 105261610685847389616054347)
              ·
                refine ⟨157892416028771084424081521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105261610685847389616054347 157892416028771084424081521)
                ·
                  refine ⟨118419312021578313318061141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157892416028771084424081521 118419312021578313318061141)
                  ·
                    refine ⟨1387726312752870859196029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118419312021578313318061141 1387726312752870859196029)
                    ·
                      rfl

theorem cell23_8107762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_8107762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107762 prefixEnd_8107762 := by exact prefixLift 8107762
  have htrace : WordTrace (prefixWord ++ tailWord_8107762) baseStart_8107762 baseEnd_8107762 := by
    simpa [prefixWord, tailWord_8107762, baseEnd_8107762] using wordTrace_append hprefix tailTrace_8107762
  have hstable : (prefixWord ++ tailWord_8107762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107762).length < 2 ^ (prefixWord ++ tailWord_8107762).sum := by decide
  have hdescent : baseEnd_8107762 < baseStart_8107762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107809 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 6]
def baseStart_8107809 : Nat := 118140960795 + 8107809 * 2 ^ 59
def prefixEnd_8107809 : Nat := 4983230072969 + 3 ^ 40 * 8107809 * 2
def baseEnd_8107809 : Nat := 462578119094374877077819

theorem tailTrace_8107809 : CollatzResearch.WordTrace tailWord_8107809 prefixEnd_8107809 462578119094374877077819 := by
  unfold tailWord_8107809
  simp only [CollatzResearch.WordTrace]
  refine ⟨295716088283800171380430481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197144058855866780920286987 295716088283800171380430481)
  ·
    refine ⟨221787066212850128535322861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295716088283800171380430481 221787066212850128535322861)
    ·
      refine ⟨83170149829818798200746073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221787066212850128535322861 83170149829818798200746073)
      ·
        refine ⟨62377612372364098650559555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83170149829818798200746073 62377612372364098650559555)
        ·
          refine ⟨93566418558546147975839333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62377612372364098650559555 93566418558546147975839333)
          ·
            refine ⟨17543703479727402745469875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93566418558546147975839333 17543703479727402745469875)
            ·
              refine ⟨26315555219591104118204813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17543703479727402745469875 26315555219591104118204813)
              ·
                refine ⟨9868333207346664044326805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26315555219591104118204813 9868333207346664044326805)
                ·
                  refine ⟨462578119094374877077819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9868333207346664044326805 462578119094374877077819)
                  ·
                    rfl

theorem cell23_8107809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_8107809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107809 prefixEnd_8107809 := by exact prefixLift 8107809
  have htrace : WordTrace (prefixWord ++ tailWord_8107809) baseStart_8107809 baseEnd_8107809 := by
    simpa [prefixWord, tailWord_8107809, baseEnd_8107809] using wordTrace_append hprefix tailTrace_8107809
  have hstable : (prefixWord ++ tailWord_8107809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107809).length < 2 ^ (prefixWord ++ tailWord_8107809).sum := by decide
  have hdescent : baseEnd_8107809 < baseStart_8107809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107859 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 6, 2]
def baseStart_8107859 : Nat := 118140960795 + 8107859 * 2 ^ 59
def prefixEnd_8107859 : Nat := 4983230072969 + 3 ^ 40 * 8107859 * 2
def baseEnd_8107859 : Nat := 4163228745882098698075141

theorem tailTrace_8107859 : CollatzResearch.WordTrace tailWord_8107859 prefixEnd_8107859 4163228745882098698075141 := by
  unfold tailWord_8107859
  simp only [CollatzResearch.WordTrace]
  refine ⟨295717911933619029919750631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197145274622412686613167087 295717911933619029919750631)
  ·
    refine ⟨443576867900428544879625947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295717911933619029919750631 443576867900428544879625947)
    ·
      refine ⟨665365301850642817319438921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443576867900428544879625947 665365301850642817319438921)
      ·
        refine ⟨499023976387982112989579191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665365301850642817319438921 499023976387982112989579191)
        ·
          refine ⟨748535964581973169484368787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499023976387982112989579191 748535964581973169484368787)
          ·
            refine ⟨1122803946872959754226553181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748535964581973169484368787 1122803946872959754226553181)
            ·
              refine ⟨421051480077359907834957443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122803946872959754226553181 421051480077359907834957443)
              ·
                refine ⟨631577220116039861752436165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421051480077359907834957443 631577220116039861752436165)
                ·
                  refine ⟨118420728771757474078581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 631577220116039861752436165 118420728771757474078581781)
                  ·
                    refine ⟨5550971661176131597433521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118420728771757474078581781 5550971661176131597433521)
                    ·
                      refine ⟨4163228745882098698075141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550971661176131597433521 4163228745882098698075141)
                      ·
                        rfl

theorem cell23_8107859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6, 2].length) (baseStart_8107859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107859 prefixEnd_8107859 := by exact prefixLift 8107859
  have htrace : WordTrace (prefixWord ++ tailWord_8107859) baseStart_8107859 baseEnd_8107859 := by
    simpa [prefixWord, tailWord_8107859, baseEnd_8107859] using wordTrace_append hprefix tailTrace_8107859
  have hstable : (prefixWord ++ tailWord_8107859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107859).length < 2 ^ (prefixWord ++ tailWord_8107859).sum := by decide
  have hdescent : baseEnd_8107859 < baseStart_8107859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107886 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_8107886 : Nat := 118140960795 + 8107886 * 2 ^ 59
def prefixEnd_8107886 : Nat := 4983230072969 + 3 ^ 40 * 8107886 * 2
def baseEnd_8107886 : Nat := 1387747536619923364145839

theorem tailTrace_8107886 : CollatzResearch.WordTrace tailWord_8107886 prefixEnd_8107886 1387747536619923364145839 := by
  unfold tailWord_8107886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964862088065151691372939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197145931136347475687322341 36964862088065151691372939)
  ·
    refine ⟨55447293132097727537059409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36964862088065151691372939 55447293132097727537059409)
    ·
      refine ⟨41585469849073295652794557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55447293132097727537059409 41585469849073295652794557)
      ·
        refine ⟨15594551193402485869797959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41585469849073295652794557 15594551193402485869797959)
        ·
          refine ⟨23391826790103728804696939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15594551193402485869797959 23391826790103728804696939)
          ·
            refine ⟨35087740185155593207045409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23391826790103728804696939 35087740185155593207045409)
            ·
              refine ⟨26315805138866694905284057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35087740185155593207045409 26315805138866694905284057)
              ·
                refine ⟨19736853854150021178963043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26315805138866694905284057 19736853854150021178963043)
                ·
                  refine ⟨29605280781225031768444565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19736853854150021178963043 29605280781225031768444565)
                  ·
                    refine ⟨1387747536619923364145839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29605280781225031768444565 1387747536619923364145839)
                    ·
                      rfl

theorem cell23_8107886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_8107886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107886 prefixEnd_8107886 := by exact prefixLift 8107886
  have htrace : WordTrace (prefixWord ++ tailWord_8107886) baseStart_8107886 baseEnd_8107886 := by
    simpa [prefixWord, tailWord_8107886, baseEnd_8107886] using wordTrace_append hprefix tailTrace_8107886
  have hstable : (prefixWord ++ tailWord_8107886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107886).length < 2 ^ (prefixWord ++ tailWord_8107886).sum := by decide
  have hdescent : baseEnd_8107886 < baseStart_8107886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107889 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_8107889 : Nat := 118140960795 + 8107889 * 2 ^ 59
def prefixEnd_8107889 : Nat := 4983230072969 + 3 ^ 40 * 8107889 * 2
def baseEnd_8107889 : Nat := 4163244150301733580700003

theorem tailTrace_8107889 : CollatzResearch.WordTrace tailWord_8107889 prefixEnd_8107889 4163244150301733580700003 := by
  unfold tailWord_8107889
  simp only [CollatzResearch.WordTrace]
  refine ⟨295719006123510345043342721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197146004082340230028895147 295719006123510345043342721)
  ·
    refine ⟨221789254592632758782507041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295719006123510345043342721 221789254592632758782507041)
    ·
      refine ⟨166341940944474569086880281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221789254592632758782507041 166341940944474569086880281)
      ·
        refine ⟨124756455708355926815160211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166341940944474569086880281 124756455708355926815160211)
        ·
          refine ⟨187134683562533890222740317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124756455708355926815160211 187134683562533890222740317)
          ·
            refine ⟨70175506335950208833527619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187134683562533890222740317 70175506335950208833527619)
            ·
              refine ⟨105263259503925313250291429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70175506335950208833527619 105263259503925313250291429)
              ·
                refine ⟨19736861156985996234429643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105263259503925313250291429 19736861156985996234429643)
                ·
                  refine ⟨29605291735478994351644465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19736861156985996234429643 29605291735478994351644465)
                  ·
                    refine ⟨22203968801609245763733349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29605291735478994351644465 22203968801609245763733349)
                    ·
                      refine ⟨4163244150301733580700003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22203968801609245763733349 4163244150301733580700003)
                      ·
                        rfl

theorem cell23_8107889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_8107889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107889 prefixEnd_8107889 := by exact prefixLift 8107889
  have htrace : WordTrace (prefixWord ++ tailWord_8107889) baseStart_8107889 baseEnd_8107889 := by
    simpa [prefixWord, tailWord_8107889, baseEnd_8107889] using wordTrace_append hprefix tailTrace_8107889
  have hstable : (prefixWord ++ tailWord_8107889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107889).length < 2 ^ (prefixWord ++ tailWord_8107889).sum := by decide
  have hdescent : baseEnd_8107889 < baseStart_8107889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107893 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_8107893 : Nat := 118140960795 + 8107893 * 2 ^ 59
def prefixEnd_8107893 : Nat := 4983230072969 + 3 ^ 40 * 8107893 * 2
def baseEnd_8107893 : Nat := 4163246204224351565049985

theorem tailTrace_8107893 : CollatzResearch.WordTrace tailWord_8107893 prefixEnd_8107893 4163246204224351565049985 := by
  unfold tailWord_8107893
  simp only [CollatzResearch.WordTrace]
  refine ⟨295719152015495853726488333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197146101343663902484325555 295719152015495853726488333)
  ·
    refine ⟨110894682005810945147433125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295719152015495853726488333 110894682005810945147433125)
    ·
      refine ⟨20792752876089552215143711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110894682005810945147433125 20792752876089552215143711)
      ·
        refine ⟨31189129314134328322715567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792752876089552215143711 31189129314134328322715567)
        ·
          refine ⟨46783693971201492484073351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31189129314134328322715567 46783693971201492484073351)
          ·
            refine ⟨70175540956802238726110027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46783693971201492484073351 70175540956802238726110027)
            ·
              refine ⟨105263311435203358089165041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70175540956802238726110027 105263311435203358089165041)
              ·
                refine ⟨78947483576402518566873781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105263311435203358089165041 78947483576402518566873781)
                ·
                  refine ⟨7401326585287736115644417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78947483576402518566873781 7401326585287736115644417)
                  ·
                    refine ⟨5550994938965802086733313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401326585287736115644417 5550994938965802086733313)
                    ·
                      refine ⟨4163246204224351565049985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550994938965802086733313 4163246204224351565049985)
                      ·
                        rfl

theorem cell23_8107893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_8107893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107893 prefixEnd_8107893 := by exact prefixLift 8107893
  have htrace : WordTrace (prefixWord ++ tailWord_8107893) baseStart_8107893 baseEnd_8107893 := by
    simpa [prefixWord, tailWord_8107893, baseEnd_8107893] using wordTrace_append hprefix tailTrace_8107893
  have hstable : (prefixWord ++ tailWord_8107893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107893).length < 2 ^ (prefixWord ++ tailWord_8107893).sum := by decide
  have hdescent : baseEnd_8107893 < baseStart_8107893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107943 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_8107943 : Nat := 118140960795 + 8107943 * 2 ^ 59
def prefixEnd_8107943 : Nat := 4983230072969 + 3 ^ 40 * 8107943 * 2
def baseEnd_8107943 : Nat := 4163271878257076369424755

theorem tailTrace_8107943 : CollatzResearch.WordTrace tailWord_8107943 prefixEnd_8107943 4163271878257076369424755 := by
  unfold tailWord_8107943
  simp only [CollatzResearch.WordTrace]
  refine ⟨295720975665314712265808483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197147317110209808177205655 295720975665314712265808483)
  ·
    refine ⟨443581463497972068398712725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295720975665314712265808483 443581463497972068398712725)
    ·
      refine ⟨20792881101467440706189659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443581463497972068398712725 20792881101467440706189659)
      ·
        refine ⟨31189321652201161059284489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20792881101467440706189659 31189321652201161059284489)
        ·
          refine ⟨23391991239150870794463367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31189321652201161059284489 23391991239150870794463367)
          ·
            refine ⟨35087986858726306191695051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23391991239150870794463367 35087986858726306191695051)
            ·
              refine ⟨52631980288089459287542577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35087986858726306191695051 52631980288089459287542577)
              ·
                refine ⟨39473985216067094465656933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52631980288089459287542577 39473985216067094465656933)
                ·
                  refine ⟨7401372228012580212310675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39473985216067094465656933 7401372228012580212310675)
                  ·
                    refine ⟨11102058342018870318466013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401372228012580212310675 11102058342018870318466013)
                    ·
                      refine ⟨4163271878257076369424755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102058342018870318466013 4163271878257076369424755)
                      ·
                        rfl

theorem cell23_8107943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_8107943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107943 prefixEnd_8107943 := by exact prefixLift 8107943
  have htrace : WordTrace (prefixWord ++ tailWord_8107943) baseStart_8107943 baseEnd_8107943 := by
    simpa [prefixWord, tailWord_8107943, baseEnd_8107943] using wordTrace_append hprefix tailTrace_8107943
  have hstable : (prefixWord ++ tailWord_8107943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107943).length < 2 ^ (prefixWord ++ tailWord_8107943).sum := by decide
  have hdescent : baseEnd_8107943 < baseStart_8107943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107950 : List Nat := [4, 1, 5, 1, 1, 2, 9]
def baseStart_8107950 : Nat := 118140960795 + 8107950 * 2 ^ 59
def prefixEnd_8107950 : Nat := 4983230072969 + 3 ^ 40 * 8107950 * 2
def baseEnd_8107950 : Nat := 51398462624958738790583

theorem tailTrace_8107950 : CollatzResearch.WordTrace tailWord_8107950 prefixEnd_8107950 51398462624958738790583 := by
  unfold tailWord_8107950
  simp only [CollatzResearch.WordTrace]
  refine ⟨36965153872036169057664163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197147487317526234974208869 36965153872036169057664163)
  ·
    refine ⟨55447730808054253586496245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36965153872036169057664163 55447730808054253586496245)
    ·
      refine ⟨5198224763255086273734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55447730808054253586496245 5198224763255086273734023)
      ·
        refine ⟨7797337144882629410601035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198224763255086273734023 7797337144882629410601035)
        ·
          refine ⟨11696005717323944115901553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797337144882629410601035 11696005717323944115901553)
          ·
            refine ⟨8772004287992958086926165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11696005717323944115901553 8772004287992958086926165)
            ·
              refine ⟨51398462624958738790583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8772004287992958086926165 51398462624958738790583)
              ·
                rfl

theorem cell23_8107950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 9].length) (baseStart_8107950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107950 prefixEnd_8107950 := by exact prefixLift 8107950
  have htrace : WordTrace (prefixWord ++ tailWord_8107950) baseStart_8107950 baseEnd_8107950 := by
    simpa [prefixWord, tailWord_8107950, baseEnd_8107950] using wordTrace_append hprefix tailTrace_8107950
  have hstable : (prefixWord ++ tailWord_8107950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107950).length < 2 ^ (prefixWord ++ tailWord_8107950).sum := by decide
  have hdescent : baseEnd_8107950 < baseStart_8107950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107979 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_8107979 : Nat := 118140960795 + 8107979 * 2 ^ 59
def prefixEnd_8107979 : Nat := 4983230072969 + 3 ^ 40 * 8107979 * 2
def baseEnd_8107979 : Nat := 4163290363560638228574589

theorem tailTrace_8107979 : CollatzResearch.WordTrace tailWord_8107979 prefixEnd_8107979 4163290363560638228574589 := by
  unfold tailWord_8107979
  simp only [CollatzResearch.WordTrace]
  refine ⟨295722288693184290414118991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197148192462122860276079327 295722288693184290414118991)
  ·
    refine ⟨443583433039776435621178487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295722288693184290414118991 443583433039776435621178487)
    ·
      refine ⟨665375149559664653431767731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443583433039776435621178487 665375149559664653431767731)
      ·
        refine ⟨998062724339496980147651597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665375149559664653431767731 998062724339496980147651597)
        ·
          refine ⟨374273521627311367555369349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 998062724339496980147651597 374273521627311367555369349)
          ·
            refine ⟨70176285305120881416631753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374273521627311367555369349 70176285305120881416631753)
            ·
              refine ⟨52632213978840661062473815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70176285305120881416631753 52632213978840661062473815)
              ·
                refine ⟨78948320968260991593710723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52632213978840661062473815 78948320968260991593710723)
                ·
                  refine ⟨118422481452391487390566085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78948320968260991593710723 118422481452391487390566085)
                  ·
                    refine ⟨22204215272323403885731141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118422481452391487390566085 22204215272323403885731141)
                    ·
                      refine ⟨4163290363560638228574589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22204215272323403885731141 4163290363560638228574589)
                      ·
                        rfl

theorem cell23_8107979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_8107979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107979 prefixEnd_8107979 := by exact prefixLift 8107979
  have htrace : WordTrace (prefixWord ++ tailWord_8107979) baseStart_8107979 baseEnd_8107979 := by
    simpa [prefixWord, tailWord_8107979, baseEnd_8107979] using wordTrace_append hprefix tailTrace_8107979
  have hstable : (prefixWord ++ tailWord_8107979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107979).length < 2 ^ (prefixWord ++ tailWord_8107979).sum := by decide
  have hdescent : baseEnd_8107979 < baseStart_8107979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108017 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_8108017 : Nat := 118140960795 + 8108017 * 2 ^ 59
def prefixEnd_8108017 : Nat := 4983230072969 + 3 ^ 40 * 8108017 * 2
def baseEnd_8108017 : Nat := 4163309875825509079899415

theorem tailTrace_8108017 : CollatzResearch.WordTrace tailWord_8108017 prefixEnd_8108017 4163309875825509079899415 := by
  unfold tailWord_8108017
  simp only [CollatzResearch.WordTrace]
  refine ⟨295723674667046622904002305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197149116444697748602668203 295723674667046622904002305)
  ·
    refine ⟨221792756000284967178001729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295723674667046622904002305 221792756000284967178001729)
    ·
      refine ⟨166344567000213725383501297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221792756000284967178001729 166344567000213725383501297)
      ·
        refine ⟨124758425250160294037625973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166344567000213725383501297 124758425250160294037625973)
        ·
          refine ⟨11696102367202527566027435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124758425250160294037625973 11696102367202527566027435)
          ·
            refine ⟨17544153550803791349041153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696102367202527566027435 17544153550803791349041153)
            ·
              refine ⟨13158115163102843511780865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17544153550803791349041153 13158115163102843511780865)
              ·
                refine ⟨9868586372327132633835649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158115163102843511780865 9868586372327132633835649)
                ·
                  refine ⟨7401439779245349475376737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868586372327132633835649 7401439779245349475376737)
                  ·
                    refine ⟨5551079834434012106532553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401439779245349475376737 5551079834434012106532553)
                    ·
                      refine ⟨4163309875825509079899415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5551079834434012106532553 4163309875825509079899415)
                      ·
                        rfl

theorem cell23_8108017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_8108017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108017 prefixEnd_8108017 := by exact prefixLift 8108017
  have htrace : WordTrace (prefixWord ++ tailWord_8108017) baseStart_8108017 baseEnd_8108017 := by
    simpa [prefixWord, tailWord_8108017, baseEnd_8108017] using wordTrace_append hprefix tailTrace_8108017
  have hstable : (prefixWord ++ tailWord_8108017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108017).length < 2 ^ (prefixWord ++ tailWord_8108017).sum := by decide
  have hdescent : baseEnd_8108017 < baseStart_8108017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108056 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_8108056 : Nat := 118140960795 + 8108056 * 2 ^ 59
def prefixEnd_8108056 : Nat := 4983230072969 + 3 ^ 40 * 8108056 * 2
def baseEnd_8108056 : Nat := 4163329901571034427311735

theorem tailTrace_8108056 : CollatzResearch.WordTrace tailWord_8108056 prefixEnd_8108056 4163329901571034427311735 := by
  unfold tailWord_8108056
  simp only [CollatzResearch.WordTrace]
  refine ⟨147862548556952666282336011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197150064742603555043114681 147862548556952666282336011)
  ·
    refine ⟨221793822835428999423504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147862548556952666282336011 221793822835428999423504017)
    ·
      refine ⟨166345367126571749567628013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221793822835428999423504017 166345367126571749567628013)
      ·
        refine ⟨62379512672464406087860505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166345367126571749567628013 62379512672464406087860505)
        ·
          refine ⟨46784634504348304565895379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62379512672464406087860505 46784634504348304565895379)
          ·
            refine ⟨70176951756522456848843069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46784634504348304565895379 70176951756522456848843069)
            ·
              refine ⟨26316356908695921318316151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70176951756522456848843069 26316356908695921318316151)
              ·
                refine ⟨39474535363043881977474227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26316356908695921318316151 39474535363043881977474227)
                ·
                  refine ⟨59211803044565822966211341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39474535363043881977474227 59211803044565822966211341)
                  ·
                    refine ⟨22204426141712183612329253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59211803044565822966211341 22204426141712183612329253)
                    ·
                      refine ⟨4163329901571034427311735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22204426141712183612329253 4163329901571034427311735)
                      ·
                        rfl

theorem cell23_8108056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_8108056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108056 prefixEnd_8108056 := by exact prefixLift 8108056
  have htrace : WordTrace (prefixWord ++ tailWord_8108056) baseStart_8108056 baseEnd_8108056 := by
    simpa [prefixWord, tailWord_8108056, baseEnd_8108056] using wordTrace_append hprefix tailTrace_8108056
  have hstable : (prefixWord ++ tailWord_8108056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108056).length < 2 ^ (prefixWord ++ tailWord_8108056).sum := by decide
  have hdescent : baseEnd_8108056 < baseStart_8108056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108059 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_8108059 : Nat := 118140960795 + 8108059 * 2 ^ 59
def prefixEnd_8108059 : Nat := 4983230072969 + 3 ^ 40 * 8108059 * 2
def baseEnd_8108059 : Nat := 4163331442012997915574221

theorem tailTrace_8108059 : CollatzResearch.WordTrace tailWord_8108059 prefixEnd_8108059 4163331442012997915574221 := by
  unfold tailWord_8108059
  simp only [CollatzResearch.WordTrace]
  refine ⟨295725206532894464077031231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197150137688596309384687487 295725206532894464077031231)
  ·
    refine ⟨443587809799341696115546847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295725206532894464077031231 443587809799341696115546847)
    ·
      refine ⟨665381714699012544173320271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443587809799341696115546847 665381714699012544173320271)
      ·
        refine ⟨998072572048518816259980407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665381714699012544173320271 998072572048518816259980407)
        ·
          refine ⟨1497108858072778224389970611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998072572048518816259980407 1497108858072778224389970611)
          ·
            refine ⟨2245663287109167336584955917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497108858072778224389970611 2245663287109167336584955917)
            ·
              refine ⟨842123732665937751219358469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245663287109167336584955917 842123732665937751219358469)
              ·
                refine ⟨157898199874863328353629713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842123732665937751219358469 157898199874863328353629713)
                ·
                  refine ⟨118423649906147496265222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157898199874863328353629713 118423649906147496265222285)
                  ·
                    refine ⟨44408868714805311099458357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118423649906147496265222285 44408868714805311099458357)
                    ·
                      refine ⟨4163331442012997915574221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44408868714805311099458357 4163331442012997915574221)
                      ·
                        rfl

theorem cell23_8108059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_8108059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108059 prefixEnd_8108059 := by exact prefixLift 8108059
  have htrace : WordTrace (prefixWord ++ tailWord_8108059) baseStart_8108059 baseEnd_8108059 := by
    simpa [prefixWord, tailWord_8108059, baseEnd_8108059] using wordTrace_append hprefix tailTrace_8108059
  have hstable : (prefixWord ++ tailWord_8108059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108059).length < 2 ^ (prefixWord ++ tailWord_8108059).sum := by decide
  have hdescent : baseEnd_8108059 < baseStart_8108059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108106 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_8108106 : Nat := 118140960795 + 8108106 * 2 ^ 59
def prefixEnd_8108106 : Nat := 4983230072969 + 3 ^ 40 * 8108106 * 2
def baseEnd_8108106 : Nat := 4163355575603759231686505

theorem tailTrace_8108106 : CollatzResearch.WordTrace tailWord_8108106 prefixEnd_8108106 4163355575603759231686505 := by
  unfold tailWord_8108106
  simp only [CollatzResearch.WordTrace]
  refine ⟨73931730190931047775998043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197151280509149460735994781 73931730190931047775998043)
  ·
    refine ⟨110897595286396571663997065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73931730190931047775998043 110897595286396571663997065)
    ·
      refine ⟨83173196464797428747997799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110897595286396571663997065 83173196464797428747997799)
      ·
        refine ⟨124759794697196143121996699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83173196464797428747997799 124759794697196143121996699)
        ·
          refine ⟨187139692045794214682995049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124759794697196143121996699 187139692045794214682995049)
          ·
            refine ⟨140354769034345661012246287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187139692045794214682995049 140354769034345661012246287)
            ·
              refine ⟨210532153551518491518369431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140354769034345661012246287 210532153551518491518369431)
              ·
                refine ⟨315798230327277737277554147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210532153551518491518369431 315798230327277737277554147)
                ·
                  refine ⟨473697345490916605916331221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315798230327277737277554147 473697345490916605916331221)
                  ·
                    refine ⟨11102281534943357951164013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 473697345490916605916331221 11102281534943357951164013)
                    ·
                      refine ⟨4163355575603759231686505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102281534943357951164013 4163355575603759231686505)
                      ·
                        rfl

theorem cell23_8108106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_8108106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108106 prefixEnd_8108106 := by exact prefixLift 8108106
  have htrace : WordTrace (prefixWord ++ tailWord_8108106) baseStart_8108106 baseEnd_8108106 := by
    simpa [prefixWord, tailWord_8108106, baseEnd_8108106] using wordTrace_append hprefix tailTrace_8108106
  have hstable : (prefixWord ++ tailWord_8108106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108106).length < 2 ^ (prefixWord ++ tailWord_8108106).sum := by decide
  have hdescent : baseEnd_8108106 < baseStart_8108106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108117 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_8108117 : Nat := 118140960795 + 8108117 * 2 ^ 59
def prefixEnd_8108117 : Nat := 4983230072969 + 3 ^ 40 * 8108117 * 2
def baseEnd_8108117 : Nat := 1387787074630319562882985

theorem tailTrace_8108117 : CollatzResearch.WordTrace tailWord_8108117 prefixEnd_8108117 1387787074630319562882985 := by
  unfold tailWord_8108117
  simp only [CollatzResearch.WordTrace]
  refine ⟨295727321966684339982642605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197151547977789559988428403 295727321966684339982642605)
  ·
    refine ⟨110897745737506627493490977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295727321966684339982642605 110897745737506627493490977)
    ·
      refine ⟨83173309303129970620118233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110897745737506627493490977 83173309303129970620118233)
      ·
        refine ⟨62379981977347477965088675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83173309303129970620118233 62379981977347477965088675)
        ·
          refine ⟨93569972966021216947633013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62379981977347477965088675 93569972966021216947633013)
          ·
            refine ⟨8772184965564489088840595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93569972966021216947633013 8772184965564489088840595)
            ·
              refine ⟨13158277448346733633260893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772184965564489088840595 13158277448346733633260893)
              ·
                refine ⟨4934354043130025112472835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13158277448346733633260893 4934354043130025112472835)
                ·
                  refine ⟨7401531064695037668709253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934354043130025112472835 7401531064695037668709253)
                  ·
                    refine ⟨1387787074630319562882985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401531064695037668709253 1387787074630319562882985)
                    ·
                      rfl

theorem cell23_8108117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_8108117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108117 prefixEnd_8108117 := by exact prefixLift 8108117
  have htrace : WordTrace (prefixWord ++ tailWord_8108117) baseStart_8108117 baseEnd_8108117 := by
    simpa [prefixWord, tailWord_8108117, baseEnd_8108117] using wordTrace_append hprefix tailTrace_8108117
  have hstable : (prefixWord ++ tailWord_8108117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108117).length < 2 ^ (prefixWord ++ tailWord_8108117).sum := by decide
  have hdescent : baseEnd_8108117 < baseStart_8108117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108140 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_8108140 : Nat := 118140960795 + 8108140 * 2 ^ 59
def prefixEnd_8108140 : Nat := 4983230072969 + 3 ^ 40 * 8108140 * 2
def baseEnd_8108140 : Nat := 4163373033946012098661349

theorem tailTrace_8108140 : CollatzResearch.WordTrace tailWord_8108140 prefixEnd_8108140 4163373033946012098661349 := by
  unfold tailWord_8108140
  simp only [CollatzResearch.WordTrace]
  refine ⟨147864080422800507455364937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197152107230400676607153249 147864080422800507455364937)
  ·
    refine ⟨110898060317100380591523703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147864080422800507455364937 110898060317100380591523703)
    ·
      refine ⟨166347090475650570887285555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110898060317100380591523703 166347090475650570887285555)
      ·
        refine ⟨249520635713475856330928333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166347090475650570887285555 249520635713475856330928333)
        ·
          refine ⟨93570238392553446124098125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249520635713475856330928333 93570238392553446124098125)
          ·
            refine ⟨35088839397207542296536797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93570238392553446124098125 35088839397207542296536797)
            ·
              refine ⟨13158314773952828361201299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35088839397207542296536797 13158314773952828361201299)
              ·
                refine ⟨19737472160929242541801949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158314773952828361201299 19737472160929242541801949)
                ·
                  refine ⟨7401552060348465953175731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19737472160929242541801949 7401552060348465953175731)
                  ·
                    refine ⟨11102328090522698929763597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401552060348465953175731 11102328090522698929763597)
                    ·
                      refine ⟨4163373033946012098661349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102328090522698929763597 4163373033946012098661349)
                      ·
                        rfl

theorem cell23_8108140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_8108140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108140 prefixEnd_8108140 := by exact prefixLift 8108140
  have htrace : WordTrace (prefixWord ++ tailWord_8108140) baseStart_8108140 baseEnd_8108140 := by
    simpa [prefixWord, tailWord_8108140, baseEnd_8108140] using wordTrace_append hprefix tailTrace_8108140
  have hstable : (prefixWord ++ tailWord_8108140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108140).length < 2 ^ (prefixWord ++ tailWord_8108140).sum := by decide
  have hdescent : baseEnd_8108140 < baseStart_8108140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108163 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4]
def baseStart_8108163 : Nat := 118140960795 + 8108163 * 2 ^ 59
def prefixEnd_8108163 : Nat := 4983230072969 + 3 ^ 40 * 8108163 * 2
def baseEnd_8108163 : Nat := 4163384844001065508673743

theorem tailTrace_8108163 : CollatzResearch.WordTrace tailWord_8108163 prefixEnd_8108163 4163384844001065508673743 := by
  unfold tailWord_8108163
  simp only [CollatzResearch.WordTrace]
  refine ⟨295728999724517689838817143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197152666483011793225878095 295728999724517689838817143)
  ·
    refine ⟨443593499586776534758225715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295728999724517689838817143 443593499586776534758225715)
    ·
      refine ⟨665390249380164802137338573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443593499586776534758225715 665390249380164802137338573)
      ·
        refine ⟨249521343517561800801501965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665390249380164802137338573 249521343517561800801501965)
        ·
          refine ⟨93570503819085675300563237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249521343517561800801501965 93570503819085675300563237)
          ·
            refine ⟨17544469466078564118855607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93570503819085675300563237 17544469466078564118855607)
            ·
              refine ⟨26316704199117846178283411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17544469466078564118855607 26316704199117846178283411)
              ·
                refine ⟨39475056298676769267425117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26316704199117846178283411 39475056298676769267425117)
                ·
                  refine ⟨14803146112003788475284419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39475056298676769267425117 14803146112003788475284419)
                  ·
                    refine ⟨22204719168005682712926629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14803146112003788475284419 22204719168005682712926629)
                    ·
                      refine ⟨4163384844001065508673743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22204719168005682712926629 4163384844001065508673743)
                      ·
                        rfl

theorem cell23_8108163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_8108163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108163 prefixEnd_8108163 := by exact prefixLift 8108163
  have htrace : WordTrace (prefixWord ++ tailWord_8108163) baseStart_8108163 baseEnd_8108163 := by
    simpa [prefixWord, tailWord_8108163, baseEnd_8108163] using wordTrace_append hprefix tailTrace_8108163
  have hstable : (prefixWord ++ tailWord_8108163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108163).length < 2 ^ (prefixWord ++ tailWord_8108163).sum := by decide
  have hdescent : baseEnd_8108163 < baseStart_8108163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108186 : List Nat := [3, 1, 1, 5, 13]
def baseStart_8108186 : Nat := 118140960795 + 8108186 * 2 ^ 59
def prefixEnd_8108186 : Nat := 4983230072969 + 3 ^ 40 * 8108186 * 2
def baseEnd_8108186 : Nat := 5711106521338983427553

theorem tailTrace_8108186 : CollatzResearch.WordTrace tailWord_8108186 prefixEnd_8108186 5711106521338983427553 := by
  unfold tailWord_8108186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73932459650858591191726103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197153225735622909844602941 73932459650858591191726103)
  ·
    refine ⟨110898689476287886787589155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73932459650858591191726103 110898689476287886787589155)
    ·
      refine ⟨166348034214431830181383733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110898689476287886787589155 166348034214431830181383733)
      ·
        refine ⟨15595128207602984079504725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166348034214431830181383733 15595128207602984079504725)
        ·
          refine ⟨5711106521338983427553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15595128207602984079504725 5711106521338983427553)
          ·
            rfl

theorem cell23_8108186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 13].length) (baseStart_8108186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108186 prefixEnd_8108186 := by exact prefixLift 8108186
  have htrace : WordTrace (prefixWord ++ tailWord_8108186) baseStart_8108186 baseEnd_8108186 := by
    simpa [prefixWord, tailWord_8108186, baseEnd_8108186] using wordTrace_append hprefix tailTrace_8108186
  have hstable : (prefixWord ++ tailWord_8108186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108186).length < 2 ^ (prefixWord ++ tailWord_8108186).sum := by decide
  have hdescent : baseEnd_8108186 < baseStart_8108186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108191 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 1, 1, 3]
def baseStart_8108191 : Nat := 118140960795 + 8108191 * 2 ^ 59
def prefixEnd_8108191 : Nat := 4983230072969 + 3 ^ 40 * 8108191 * 2
def baseEnd_8108191 : Nat := 4163399221459391399123615

theorem tailTrace_8108191 : CollatzResearch.WordTrace tailWord_8108191 prefixEnd_8108191 4163399221459391399123615 := by
  unfold tailWord_8108191
  simp only [CollatzResearch.WordTrace]
  refine ⟨295730020968416250620836427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197153347312277500413890951 295730020968416250620836427)
  ·
    refine ⟨443595031452624375931254641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295730020968416250620836427 443595031452624375931254641)
    ·
      refine ⟨332696273589468281948440981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443595031452624375931254641 332696273589468281948440981)
      ·
        refine ⟨15595137824506325716333171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332696273589468281948440981 15595137824506325716333171)
        ·
          refine ⟨23392706736759488574499757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595137824506325716333171 23392706736759488574499757)
          ·
            refine ⟨8772265026284808215437409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23392706736759488574499757 8772265026284808215437409)
            ·
              refine ⟨6579198769713606161578057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772265026284808215437409 6579198769713606161578057)
              ·
                refine ⟨4934399077285204621183543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6579198769713606161578057 4934399077285204621183543)
                ·
                  refine ⟨7401598615927806931775315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934399077285204621183543 7401598615927806931775315)
                  ·
                    refine ⟨11102397923891710397662973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401598615927806931775315 11102397923891710397662973)
                    ·
                      refine ⟨4163399221459391399123615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102397923891710397662973 4163399221459391399123615)
                      ·
                        rfl

theorem cell23_8108191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_8108191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108191 prefixEnd_8108191 := by exact prefixLift 8108191
  have htrace : WordTrace (prefixWord ++ tailWord_8108191) baseStart_8108191 baseEnd_8108191 := by
    simpa [prefixWord, tailWord_8108191, baseEnd_8108191] using wordTrace_append hprefix tailTrace_8108191
  have hstable : (prefixWord ++ tailWord_8108191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108191).length < 2 ^ (prefixWord ++ tailWord_8108191).sum := by decide
  have hdescent : baseEnd_8108191 < baseStart_8108191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108216 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_8108216 : Nat := 118140960795 + 8108216 * 2 ^ 59
def prefixEnd_8108216 : Nat := 4983230072969 + 3 ^ 40 * 8108216 * 2
def baseEnd_8108216 : Nat := 1387804019491917933770333

theorem tailTrace_8108216 : CollatzResearch.WordTrace tailWord_8108216 prefixEnd_8108216 1387804019491917933770333 := by
  unfold tailWord_8108216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147865466396662839945248251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197153955195550453260331001 147865466396662839945248251)
  ·
    refine ⟨221798199594994259917872377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147865466396662839945248251 221798199594994259917872377)
    ·
      refine ⟨166348649696245694938404283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221798199594994259917872377 166348649696245694938404283)
      ·
        refine ⟨249522974544368542407606425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166348649696245694938404283 249522974544368542407606425)
        ·
          refine ⟨187142230908276406805704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249522974544368542407606425 187142230908276406805704819)
          ·
            refine ⟨280713346362414610208557229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187142230908276406805704819 280713346362414610208557229)
            ·
              refine ⟨105267504885905478828208961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280713346362414610208557229 105267504885905478828208961)
              ·
                refine ⟨78950628664429109121156721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105267504885905478828208961 78950628664429109121156721)
                ·
                  refine ⟨59212971498321831840867541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78950628664429109121156721 59212971498321831840867541)
                  ·
                    refine ⟨1387804019491917933770333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59212971498321831840867541 1387804019491917933770333)
                    ·
                      rfl

theorem cell23_8108216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_8108216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108216 prefixEnd_8108216 := by exact prefixLift 8108216
  have htrace : WordTrace (prefixWord ++ tailWord_8108216) baseStart_8108216 baseEnd_8108216 := by
    simpa [prefixWord, tailWord_8108216, baseEnd_8108216] using wordTrace_append hprefix tailTrace_8108216
  have hstable : (prefixWord ++ tailWord_8108216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108216).length < 2 ^ (prefixWord ++ tailWord_8108216).sum := by decide
  have hdescent : baseEnd_8108216 < baseStart_8108216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108220 : List Nat := [2, 2, 2, 3, 3, 1, 3, 7]
def baseStart_8108220 : Nat := 118140960795 + 8108220 * 2 ^ 59
def prefixEnd_8108220 : Nat := 4983230072969 + 3 ^ 40 * 8108220 * 2
def baseEnd_8108220 : Nat := 154200522681421177246703

theorem tailTrace_8108220 : CollatzResearch.WordTrace tailWord_8108220 prefixEnd_8108220 154200522681421177246703 := by
  unfold tailWord_8108220
  simp only [CollatzResearch.WordTrace]
  refine ⟨147865539342655594286821057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197154052456874125715761409 147865539342655594286821057)
  ·
    refine ⟨110899154506991695715115793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147865539342655594286821057 110899154506991695715115793)
    ·
      refine ⟨83174365880243771786336845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110899154506991695715115793 83174365880243771786336845)
      ·
        refine ⟨31190387205091414419876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83174365880243771786336845 31190387205091414419876317)
        ·
          refine ⟨11696395201909280407453619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31190387205091414419876317 11696395201909280407453619)
          ·
            refine ⟨17544592802863920611180429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696395201909280407453619 17544592802863920611180429)
            ·
              refine ⟨6579222301073970229192661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544592802863920611180429 6579222301073970229192661)
              ·
                refine ⟨154200522681421177246703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6579222301073970229192661 154200522681421177246703)
                ·
                  rfl

theorem cell23_8108220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 7].length) (baseStart_8108220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108220 prefixEnd_8108220 := by exact prefixLift 8108220
  have htrace : WordTrace (prefixWord ++ tailWord_8108220) baseStart_8108220 baseEnd_8108220 := by
    simpa [prefixWord, tailWord_8108220, baseEnd_8108220] using wordTrace_append hprefix tailTrace_8108220
  have hstable : (prefixWord ++ tailWord_8108220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108220).length < 2 ^ (prefixWord ++ tailWord_8108220).sum := by decide
  have hdescent : baseEnd_8108220 < baseStart_8108220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108258 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8108258 : Nat := 118140960795 + 8108258 * 2 ^ 59
def prefixEnd_8108258 : Nat := 4983230072969 + 3 ^ 40 * 8108258 * 2
def baseEnd_8108258 : Nat := 1387811208221080878995269

theorem tailTrace_8108258 : CollatzResearch.WordTrace tailWord_8108258 prefixEnd_8108258 1387811208221080878995269 := by
  unfold tailWord_8108258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933116164793380265881357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197154976439449014042350285 73933116164793380265881357)
  ·
    refine ⟨27724918561797517599705509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73933116164793380265881357 27724918561797517599705509)
    ·
      refine ⟨5198422230337034549944783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27724918561797517599705509 5198422230337034549944783)
      ·
        refine ⟨7797633345505551824917175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198422230337034549944783 7797633345505551824917175)
        ·
          refine ⟨11696450018258327737375763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797633345505551824917175 11696450018258327737375763)
          ·
            refine ⟨17544675027387491606063645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696450018258327737375763 17544675027387491606063645)
            ·
              refine ⟨6579253135270309352273867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544675027387491606063645 6579253135270309352273867)
              ·
                refine ⟨9868879702905464028410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579253135270309352273867 9868879702905464028410801)
                ·
                  refine ⟨7401659777179098021308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868879702905464028410801 7401659777179098021308101)
                  ·
                    refine ⟨1387811208221080878995269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401659777179098021308101 1387811208221080878995269)
                    ·
                      rfl

theorem cell23_8108258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8108258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108258 prefixEnd_8108258 := by exact prefixLift 8108258
  have htrace : WordTrace (prefixWord ++ tailWord_8108258) baseStart_8108258 baseEnd_8108258 := by
    simpa [prefixWord, tailWord_8108258, baseEnd_8108258] using wordTrace_append hprefix tailTrace_8108258
  have hstable : (prefixWord ++ tailWord_8108258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108258).length < 2 ^ (prefixWord ++ tailWord_8108258).sum := by decide
  have hdescent : baseEnd_8108258 < baseStart_8108258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108264 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_8108264 : Nat := 118140960795 + 8108264 * 2 ^ 59
def prefixEnd_8108264 : Nat := 4983230072969 + 3 ^ 40 * 8108264 * 2
def baseEnd_8108264 : Nat := 4163436705547169613510779

theorem tailTrace_8108264 : CollatzResearch.WordTrace tailWord_8108264 prefixEnd_8108264 4163436705547169613510779 := by
  unfold tailWord_8108264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147866341748575892044121923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197155122331434522725495897 147866341748575892044121923)
  ·
    refine ⟨221799512622863838066182885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147866341748575892044121923 221799512622863838066182885)
    ·
      refine ⟨41587408616786969637409291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221799512622863838066182885 41587408616786969637409291)
      ·
        refine ⟨62381112925180454456113937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41587408616786969637409291 62381112925180454456113937)
        ·
          refine ⟨46785834693885340842085453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62381112925180454456113937 46785834693885340842085453)
          ·
            refine ⟨17544688010207002815782045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46785834693885340842085453 17544688010207002815782045)
            ·
              refine ⟨6579258003827626055918267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544688010207002815782045 6579258003827626055918267)
              ·
                refine ⟨9868887005741439083877401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579258003827626055918267 9868887005741439083877401)
                ·
                  refine ⟨7401665254306079312908051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868887005741439083877401 7401665254306079312908051)
                  ·
                    refine ⟨11102497881459118969362077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401665254306079312908051 11102497881459118969362077)
                    ·
                      refine ⟨4163436705547169613510779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102497881459118969362077 4163436705547169613510779)
                      ·
                        rfl

theorem cell23_8108264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_8108264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108264 prefixEnd_8108264 := by exact prefixLift 8108264
  have htrace : WordTrace (prefixWord ++ tailWord_8108264) baseStart_8108264 baseEnd_8108264 := by
    simpa [prefixWord, tailWord_8108264, baseEnd_8108264] using wordTrace_append hprefix tailTrace_8108264
  have hstable : (prefixWord ++ tailWord_8108264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108264).length < 2 ^ (prefixWord ++ tailWord_8108264).sum := by decide
  have hdescent : baseEnd_8108264 < baseStart_8108264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108273 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_8108273 : Nat := 118140960795 + 8108273 * 2 ^ 59
def prefixEnd_8108273 : Nat := 4983230072969 + 3 ^ 40 * 8108273 * 2
def baseEnd_8108273 : Nat := 4163441326873060078298237

theorem tailTrace_8108273 : CollatzResearch.WordTrace tailWord_8108273 prefixEnd_8108273 4163441326873060078298237 := by
  unfold tailWord_8108273
  simp only [CollatzResearch.WordTrace]
  refine ⟨295733011754119178625321473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197155341169412785750214315 295733011754119178625321473)
  ·
    refine ⟨221799758815589383968991105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295733011754119178625321473 221799758815589383968991105)
    ·
      refine ⟨166349819111692037976743329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221799758815589383968991105 166349819111692037976743329)
      ·
        refine ⟨124762364333769028482557497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166349819111692037976743329 124762364333769028482557497)
        ·
          refine ⟨93571773250326771361918123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124762364333769028482557497 93571773250326771361918123)
          ·
            refine ⟨140357659875490157042877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93571773250326771361918123 140357659875490157042877185)
            ·
              refine ⟨105268244906617617782157889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140357659875490157042877185 105268244906617617782157889)
              ·
                refine ⟨78951183679963213336618417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105268244906617617782157889 78951183679963213336618417)
                ·
                  refine ⟨59213387759972410002463813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78951183679963213336618417 59213387759972410002463813)
                  ·
                    refine ⟨11102510204994826875461965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59213387759972410002463813 11102510204994826875461965)
                    ·
                      refine ⟨4163441326873060078298237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102510204994826875461965 4163441326873060078298237)
                      ·
                        rfl

theorem cell23_8108273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_8108273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108273 prefixEnd_8108273 := by exact prefixLift 8108273
  have htrace : WordTrace (prefixWord ++ tailWord_8108273) baseStart_8108273 baseEnd_8108273 := by
    simpa [prefixWord, tailWord_8108273, baseEnd_8108273] using wordTrace_append hprefix tailTrace_8108273
  have hstable : (prefixWord ++ tailWord_8108273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108273).length < 2 ^ (prefixWord ++ tailWord_8108273).sum := by decide
  have hdescent : baseEnd_8108273 < baseStart_8108273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108274 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_8108274 : Nat := 118140960795 + 8108274 * 2 ^ 59
def prefixEnd_8108274 : Nat := 4983230072969 + 3 ^ 40 * 8108274 * 2
def baseEnd_8108274 : Nat := 4163441840353714574385733

theorem tailTrace_8108274 : CollatzResearch.WordTrace tailWord_8108274 prefixEnd_8108274 4163441840353714574385733 := by
  unfold tailWord_8108274
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933262056778888949026969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197155365484743703864071917 73933262056778888949026969)
  ·
    refine ⟨55449946542584166711770227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73933262056778888949026969 55449946542584166711770227)
    ·
      refine ⟨83174919813876250067655341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55449946542584166711770227 83174919813876250067655341)
      ·
        refine ⟨31190594930203593775370753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83174919813876250067655341 31190594930203593775370753)
        ·
          refine ⟨23392946197652695331528065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31190594930203593775370753 23392946197652695331528065)
          ·
            refine ⟨17544709648239521498646049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23392946197652695331528065 17544709648239521498646049)
            ·
              refine ⟨13158532236179641123984537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17544709648239521498646049 13158532236179641123984537)
              ·
                refine ⟨9868899177134730842988403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158532236179641123984537 9868899177134730842988403)
                ·
                  refine ⟨14803348765702096264482605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868899177134730842988403 14803348765702096264482605)
                  ·
                    refine ⟨5551255787138286099180977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14803348765702096264482605 5551255787138286099180977)
                    ·
                      refine ⟨4163441840353714574385733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5551255787138286099180977 4163441840353714574385733)
                      ·
                        rfl

theorem cell23_8108274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_8108274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108274 prefixEnd_8108274 := by exact prefixLift 8108274
  have htrace : WordTrace (prefixWord ++ tailWord_8108274) baseStart_8108274 baseEnd_8108274 := by
    simpa [prefixWord, tailWord_8108274, baseEnd_8108274] using wordTrace_append hprefix tailTrace_8108274
  have hstable : (prefixWord ++ tailWord_8108274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108274).length < 2 ^ (prefixWord ++ tailWord_8108274).sum := by decide
  have hdescent : baseEnd_8108274 < baseStart_8108274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108290 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8108290 : Nat := 118140960795 + 8108290 * 2 ^ 59
def prefixEnd_8108290 : Nat := 4983230072969 + 3 ^ 40 * 8108290 * 2
def baseEnd_8108290 : Nat := 4163450056044186511785659

theorem tailTrace_8108290 : CollatzResearch.WordTrace tailWord_8108290 prefixEnd_8108290 4163450056044186511785659 := by
  unfold tailWord_8108290
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933407948764397632172581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197155754530038393685793549 73933407948764397632172581)
  ·
    refine ⟨13862513990393324556032359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73933407948764397632172581 13862513990393324556032359)
    ·
      refine ⟨20793770985589986834048539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13862513990393324556032359 20793770985589986834048539)
      ·
        refine ⟨31190656478384980251072809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20793770985589986834048539 31190656478384980251072809)
        ·
          refine ⟨23392992358788735188304607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31190656478384980251072809 23392992358788735188304607)
          ·
            refine ⟨35089488538183102782456911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23392992358788735188304607 35089488538183102782456911)
            ·
              refine ⟨52634232807274654173685367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35089488538183102782456911 52634232807274654173685367)
              ·
                refine ⟨78951349210911981260528051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52634232807274654173685367 78951349210911981260528051)
                ·
                  refine ⟨118427023816367971890792077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78951349210911981260528051 118427023816367971890792077)
                  ·
                    refine ⟨44410133931137989459047029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118427023816367971890792077 44410133931137989459047029)
                    ·
                      refine ⟨4163450056044186511785659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44410133931137989459047029 4163450056044186511785659)
                      ·
                        rfl

theorem cell23_8108290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8108290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108290 prefixEnd_8108290 := by exact prefixLift 8108290
  have htrace : WordTrace (prefixWord ++ tailWord_8108290) baseStart_8108290 baseEnd_8108290 := by
    simpa [prefixWord, tailWord_8108290, baseEnd_8108290] using wordTrace_append hprefix tailTrace_8108290
  have hstable : (prefixWord ++ tailWord_8108290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108290).length < 2 ^ (prefixWord ++ tailWord_8108290).sum := by decide
  have hdescent : baseEnd_8108290 < baseStart_8108290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108303 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_8108303 : Nat := 118140960795 + 8108303 * 2 ^ 59
def prefixEnd_8108303 : Nat := 4983230072969 + 3 ^ 40 * 8108303 * 2
def baseEnd_8108303 : Nat := 4163456731292694960923099

theorem tailTrace_8108303 : CollatzResearch.WordTrace tailWord_8108303 prefixEnd_8108303 4163456731292694960923099 := by
  unfold tailWord_8108303
  simp only [CollatzResearch.WordTrace]
  refine ⟨295734105944010493748913563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197156070629340329165942375 295734105944010493748913563)
  ·
    refine ⟨443601158916015740623370345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295734105944010493748913563 443601158916015740623370345)
    ·
      refine ⟨332700869187011805467527759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443601158916015740623370345 332700869187011805467527759)
      ·
        refine ⟨499051303780517708201291639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332700869187011805467527759 499051303780517708201291639)
        ·
          refine ⟨748576955670776562301937459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499051303780517708201291639 748576955670776562301937459)
          ·
            refine ⟨1122865433506164843452906189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748576955670776562301937459 1122865433506164843452906189)
            ·
              refine ⟨421074537564811816294839821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122865433506164843452906189 421074537564811816294839821)
              ·
                refine ⟨157902951586804431110564933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421074537564811816294839821 157902951586804431110564933)
                ·
                  refine ⟨29606803422525830833230925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157902951586804431110564933 29606803422525830833230925)
                  ·
                    refine ⟨11102551283447186562461597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29606803422525830833230925 11102551283447186562461597)
                    ·
                      refine ⟨4163456731292694960923099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102551283447186562461597 4163456731292694960923099)
                      ·
                        rfl

theorem cell23_8108303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_8108303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108303 prefixEnd_8108303 := by exact prefixLift 8108303
  have htrace : WordTrace (prefixWord ++ tailWord_8108303) baseStart_8108303 baseEnd_8108303 := by
    simpa [prefixWord, tailWord_8108303, baseEnd_8108303] using wordTrace_append hprefix tailTrace_8108303
  have hstable : (prefixWord ++ tailWord_8108303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108303).length < 2 ^ (prefixWord ++ tailWord_8108303).sum := by decide
  have hdescent : baseEnd_8108303 < baseStart_8108303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108323 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 4, 5]
def baseStart_8108323 : Nat := 118140960795 + 8108323 * 2 ^ 59
def prefixEnd_8108323 : Nat := 4983230072969 + 3 ^ 40 * 8108323 * 2
def baseEnd_8108323 : Nat := 1387822333635261627557669

theorem tailTrace_8108323 : CollatzResearch.WordTrace tailWord_8108323 prefixEnd_8108323 1387822333635261627557669 := by
  unfold tailWord_8108323
  simp only [CollatzResearch.WordTrace]
  refine ⟨295734835403938037164641623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197156556935958691443094415 295734835403938037164641623)
  ·
    refine ⟨443602253105907055746962435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295734835403938037164641623 443602253105907055746962435)
    ·
      refine ⟨665403379658860583620443653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443602253105907055746962435 665403379658860583620443653)
      ·
        refine ⟨124763133686036359428833185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665403379658860583620443653 124763133686036359428833185)
        ·
          refine ⟨93572350264527269571624889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124763133686036359428833185 93572350264527269571624889)
          ·
            refine ⟨70179262698395452178718667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93572350264527269571624889 70179262698395452178718667)
            ·
              refine ⟨105268894047593178268078001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70179262698395452178718667 105268894047593178268078001)
              ·
                refine ⟨78951670535694883701058501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105268894047593178268078001 78951670535694883701058501)
                ·
                  refine ⟨14803438225442790693948469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78951670535694883701058501 14803438225442790693948469)
                  ·
                    refine ⟨1387822333635261627557669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14803438225442790693948469 1387822333635261627557669)
                    ·
                      rfl

theorem cell23_8108323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].length) (baseStart_8108323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108323 prefixEnd_8108323 := by exact prefixLift 8108323
  have htrace : WordTrace (prefixWord ++ tailWord_8108323) baseStart_8108323 baseEnd_8108323 := by
    simpa [prefixWord, tailWord_8108323, baseEnd_8108323] using wordTrace_append hprefix tailTrace_8108323
  have hstable : (prefixWord ++ tailWord_8108323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108323).length < 2 ^ (prefixWord ++ tailWord_8108323).sum := by decide
  have hdescent : baseEnd_8108323 < baseStart_8108323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108343 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_8108343 : Nat := 118140960795 + 8108343 * 2 ^ 59
def prefixEnd_8108343 : Nat := 4983230072969 + 3 ^ 40 * 8108343 * 2
def baseEnd_8108343 : Nat := 4163477270518874804422915

theorem tailTrace_8108343 : CollatzResearch.WordTrace tailWord_8108343 prefixEnd_8108343 4163477270518874804422915 := by
  unfold tailWord_8108343
  simp only [CollatzResearch.WordTrace]
  refine ⟨295735564863865580580369683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197157043242577053720246455 295735564863865580580369683)
  ·
    refine ⟨443603347295798370870554525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295735564863865580580369683 443603347295798370870554525)
    ·
      refine ⟨166351255235924389076457947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443603347295798370870554525 166351255235924389076457947)
      ·
        refine ⟨249526882853886583614686921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166351255235924389076457947 249526882853886583614686921)
        ·
          refine ⟨187145162140414937711015191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249526882853886583614686921 187145162140414937711015191)
          ·
            refine ⟨280717743210622406566522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187145162140414937711015191 280717743210622406566522787)
            ·
              refine ⟨421076614815933609849784181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280717743210622406566522787 421076614815933609849784181)
              ·
                refine ⟨39475932638993775923417267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421076614815933609849784181 39475932638993775923417267)
                ·
                  refine ⟨59213898958490663885125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39475932638993775923417267 59213898958490663885125901)
                  ·
                    refine ⟨22205212109433998956922213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59213898958490663885125901 22205212109433998956922213)
                    ·
                      refine ⟨4163477270518874804422915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22205212109433998956922213 4163477270518874804422915)
                      ·
                        rfl

theorem cell23_8108343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_8108343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108343 prefixEnd_8108343 := by exact prefixLift 8108343
  have htrace : WordTrace (prefixWord ++ tailWord_8108343) baseStart_8108343 baseEnd_8108343 := by
    simpa [prefixWord, tailWord_8108343, baseEnd_8108343] using wordTrace_append hprefix tailTrace_8108343
  have hstable : (prefixWord ++ tailWord_8108343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108343).length < 2 ^ (prefixWord ++ tailWord_8108343).sum := by decide
  have hdescent : baseEnd_8108343 < baseStart_8108343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108350 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_8108350 : Nat := 118140960795 + 8108350 * 2 ^ 59
def prefixEnd_8108350 : Nat := 4983230072969 + 3 ^ 40 * 8108350 * 2
def baseEnd_8108350 : Nat := 4163480864883456277035383

theorem tailTrace_8108350 : CollatzResearch.WordTrace tailWord_8108350 prefixEnd_8108350 4163480864883456277035383 := by
  unfold tailWord_8108350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36966977521855027596984313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197157213449893480517249669 36966977521855027596984313)
  ·
    refine ⟨27725233141391270697738235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36966977521855027596984313 27725233141391270697738235)
    ·
      refine ⟨41587849712086906046607353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27725233141391270697738235 41587849712086906046607353)
      ·
        refine ⟨31190887284065179534955515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41587849712086906046607353 31190887284065179534955515)
        ·
          refine ⟨46786330926097769302433273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31190887284065179534955515 46786330926097769302433273)
          ·
            refine ⟨35089748194573326976824955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46786330926097769302433273 35089748194573326976824955)
            ·
              refine ⟨52634622291859990465237433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35089748194573326976824955 52634622291859990465237433)
              ·
                refine ⟨39475966718894992848928075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52634622291859990465237433 39475966718894992848928075)
                ·
                  refine ⟨59213950078342489273392113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39475966718894992848928075 59213950078342489273392113)
                  ·
                    refine ⟨44410462558756866955044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59213950078342489273392113 44410462558756866955044085)
                    ·
                      refine ⟨4163480864883456277035383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44410462558756866955044085 4163480864883456277035383)
                      ·
                        rfl

theorem cell23_8108350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_8108350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108350 prefixEnd_8108350 := by exact prefixLift 8108350
  have htrace : WordTrace (prefixWord ++ tailWord_8108350) baseStart_8108350 baseEnd_8108350 := by
    simpa [prefixWord, tailWord_8108350, baseEnd_8108350] using wordTrace_append hprefix tailTrace_8108350
  have hstable : (prefixWord ++ tailWord_8108350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108350).length < 2 ^ (prefixWord ++ tailWord_8108350).sum := by decide
  have hdescent : baseEnd_8108350 < baseStart_8108350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108360 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_8108360 : Nat := 118140960795 + 8108360 * 2 ^ 59
def prefixEnd_8108360 : Nat := 4983230072969 + 3 ^ 40 * 8108360 * 2
def baseEnd_8108360 : Nat := 4163485999690001237910337

theorem tailTrace_8108360 : CollatzResearch.WordTrace tailWord_8108360 prefixEnd_8108360 4163485999690001237910337 := by
  unfold tailWord_8108360
  simp only [CollatzResearch.WordTrace]
  refine ⟨147868092452401996241869267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197157456603202661655825689 147868092452401996241869267)
  ·
    refine ⟨221802138678602994362803901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147868092452401996241869267 221802138678602994362803901)
    ·
      refine ⟨83175802004476122886051463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221802138678602994362803901 83175802004476122886051463)
      ·
        refine ⟨124763703006714184329077195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83175802004476122886051463 124763703006714184329077195)
        ·
          refine ⟨187145554510071276493615793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124763703006714184329077195 187145554510071276493615793)
          ·
            refine ⟨140359165882553457370211845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187145554510071276493615793 140359165882553457370211845)
            ·
              refine ⟨26317343602978773256914721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140359165882553457370211845 26317343602978773256914721)
              ·
                refine ⟨19738007702234079942686041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26317343602978773256914721 19738007702234079942686041)
                ·
                  refine ⟨14803505776675559957014531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19738007702234079942686041 14803505776675559957014531)
                  ·
                    refine ⟨22205258665013339935521797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14803505776675559957014531 22205258665013339935521797)
                    ·
                      refine ⟨4163485999690001237910337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22205258665013339935521797 4163485999690001237910337)
                      ·
                        rfl

theorem cell23_8108360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_8108360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108360 prefixEnd_8108360 := by exact prefixLift 8108360
  have htrace : WordTrace (prefixWord ++ tailWord_8108360) baseStart_8108360 baseEnd_8108360 := by
    simpa [prefixWord, tailWord_8108360, baseEnd_8108360] using wordTrace_append hprefix tailTrace_8108360
  have hstable : (prefixWord ++ tailWord_8108360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108360).length < 2 ^ (prefixWord ++ tailWord_8108360).sum := by decide
  have hdescent : baseEnd_8108360 < baseStart_8108360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108394 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_8108394 : Nat := 118140960795 + 8108394 * 2 ^ 59
def prefixEnd_8108394 : Nat := 4983230072969 + 3 ^ 40 * 8108394 * 2
def baseEnd_8108394 : Nat := 4163503458032254104885181

theorem tailTrace_8108394 : CollatzResearch.WordTrace tailWord_8108394 prefixEnd_8108394 4163503458032254104885181 := by
  unfold tailWord_8108394
  simp only [CollatzResearch.WordTrace]
  refine ⟨73934356246670204072619059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197158283324453877526984157 73934356246670204072619059)
  ·
    refine ⟨110901534370005306108928589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73934356246670204072619059 110901534370005306108928589)
    ·
      refine ⟨41588075388751989790848221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110901534370005306108928589 41588075388751989790848221)
      ·
        refine ⟨15595528270781996171568083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41588075388751989790848221 15595528270781996171568083)
        ·
          refine ⟨23393292406172994257352125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595528270781996171568083 23393292406172994257352125)
          ·
            refine ⟨8772484652314872846507047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23393292406172994257352125 8772484652314872846507047)
            ·
              refine ⟨13158726978472309269760571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772484652314872846507047 13158726978472309269760571)
              ·
                refine ⟨19738090467708463904640857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158726978472309269760571 19738090467708463904640857)
                ·
                  refine ⟨14803567850781347928480643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19738090467708463904640857 14803567850781347928480643)
                  ·
                    refine ⟨22205351776172021892720965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14803567850781347928480643 22205351776172021892720965)
                    ·
                      refine ⟨4163503458032254104885181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22205351776172021892720965 4163503458032254104885181)
                      ·
                        rfl

theorem cell23_8108394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_8108394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108394 prefixEnd_8108394 := by exact prefixLift 8108394
  have htrace : WordTrace (prefixWord ++ tailWord_8108394) baseStart_8108394 baseEnd_8108394 := by
    simpa [prefixWord, tailWord_8108394, baseEnd_8108394] using wordTrace_append hprefix tailTrace_8108394
  have hstable : (prefixWord ++ tailWord_8108394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108394).length < 2 ^ (prefixWord ++ tailWord_8108394).sum := by decide
  have hdescent : baseEnd_8108394 < baseStart_8108394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108417 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 6]
def baseStart_8108417 : Nat := 118140960795 + 8108417 * 2 ^ 59
def prefixEnd_8108417 : Nat := 4983230072969 + 3 ^ 40 * 8108417 * 2
def baseEnd_8108417 : Nat := 462612807565256390544175

theorem tailTrace_8108417 : CollatzResearch.WordTrace tailWord_8108417 prefixEnd_8108417 462612807565256390544175 := by
  unfold tailWord_8108417
  simp only [CollatzResearch.WordTrace]
  refine ⟨295738263865597491218563505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197158842577064994145709003 295738263865597491218563505)
  ·
    refine ⟨221803697899198118413922629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295738263865597491218563505 221803697899198118413922629)
    ·
      refine ⟨41588193356099647202610493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221803697899198118413922629 41588193356099647202610493)
      ·
        refine ⟨15595572508537367700978935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41588193356099647202610493 15595572508537367700978935)
        ·
          refine ⟨23393358762806051551468403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595572508537367700978935 23393358762806051551468403)
          ·
            refine ⟨35090038144209077327202605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23393358762806051551468403 35090038144209077327202605)
            ·
              refine ⟨13158764304078403997700977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35090038144209077327202605 13158764304078403997700977)
              ·
                refine ⟨9869073228058802998275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158764304078403997700977 9869073228058802998275733)
                ·
                  refine ⟨462612807565256390544175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9869073228058802998275733 462612807565256390544175)
                  ·
                    rfl

theorem cell23_8108417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_8108417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108417 prefixEnd_8108417 := by exact prefixLift 8108417
  have htrace : WordTrace (prefixWord ++ tailWord_8108417) baseStart_8108417 baseEnd_8108417 := by
    simpa [prefixWord, tailWord_8108417, baseEnd_8108417] using wordTrace_append hprefix tailTrace_8108417
  have hstable : (prefixWord ++ tailWord_8108417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108417).length < 2 ^ (prefixWord ++ tailWord_8108417).sum := by decide
  have hdescent : baseEnd_8108417 < baseStart_8108417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108427 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 3]
def baseStart_8108427 : Nat := 118140960795 + 8108427 * 2 ^ 59
def prefixEnd_8108427 : Nat := 4983230072969 + 3 ^ 40 * 8108427 * 2
def baseEnd_8108427 : Nat := 4163520402893852475772529

theorem tailTrace_8108427 : CollatzResearch.WordTrace tailWord_8108427 prefixEnd_8108427 4163520402893852475772529 := by
  unfold tailWord_8108427
  simp only [CollatzResearch.WordTrace]
  refine ⟨295738628595561262926427535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197159085730374175284285023 295738628595561262926427535)
  ·
    refine ⟨443607942893341894389641303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295738628595561262926427535 443607942893341894389641303)
    ·
      refine ⟨665411914340012841584461955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443607942893341894389641303 665411914340012841584461955)
      ·
        refine ⟨998117871510019262376692933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665411914340012841584461955 998117871510019262376692933)
        ·
          refine ⟨187147100908128611695629925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 998117871510019262376692933 187147100908128611695629925)
          ·
            refine ⟨35090081420274114692930611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187147100908128611695629925 35090081420274114692930611)
            ·
              refine ⟨52635122130411172039395917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35090081420274114692930611 52635122130411172039395917)
              ·
                refine ⟨19738170798904189514773469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52635122130411172039395917 19738170798904189514773469)
                ·
                  refine ⟨7401814049589071068040051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19738170798904189514773469 7401814049589071068040051)
                  ·
                    refine ⟨11102721074383606602060077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7401814049589071068040051 11102721074383606602060077)
                    ·
                      refine ⟨4163520402893852475772529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102721074383606602060077 4163520402893852475772529)
                      ·
                        rfl

theorem cell23_8108427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 1, 3].length) (baseStart_8108427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108427 prefixEnd_8108427 := by exact prefixLift 8108427
  have htrace : WordTrace (prefixWord ++ tailWord_8108427) baseStart_8108427 baseEnd_8108427 := by
    simpa [prefixWord, tailWord_8108427, baseEnd_8108427] using wordTrace_append hprefix tailTrace_8108427
  have hstable : (prefixWord ++ tailWord_8108427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108427).length < 2 ^ (prefixWord ++ tailWord_8108427).sum := by decide
  have hdescent : baseEnd_8108427 < baseStart_8108427 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108447 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 1, 5]
def baseStart_8108447 : Nat := 118140960795 + 8108447 * 2 ^ 59
def prefixEnd_8108447 : Nat := 4983230072969 + 3 ^ 40 * 8108447 * 2
def baseEnd_8108447 : Nat := 1387843557502314132507479

theorem tailTrace_8108447 : CollatzResearch.WordTrace tailWord_8108447 prefixEnd_8108447 1387843557502314132507479 := by
  unfold tailWord_8108447
  simp only [CollatzResearch.WordTrace]
  refine ⟨295739358055488806342155595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197159572036992537561437063 295739358055488806342155595)
  ·
    refine ⟨443609037083233209513233393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295739358055488806342155595 443609037083233209513233393)
    ·
      refine ⟨332706777812424907134925045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443609037083233209513233393 332706777812424907134925045)
      ·
        refine ⟨31191260419914835043899223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332706777812424907134925045 31191260419914835043899223)
        ·
          refine ⟨46786890629872252565848835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31191260419914835043899223 46786890629872252565848835)
          ·
            refine ⟨70180335944808378848773253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46786890629872252565848835 70180335944808378848773253)
            ·
              refine ⟨13158812989651571034144985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70180335944808378848773253 13158812989651571034144985)
              ·
                refine ⟨9869109742238678275608739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158812989651571034144985 9869109742238678275608739)
                ·
                  refine ⟨14803664613358017413413109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869109742238678275608739 14803664613358017413413109)
                  ·
                    refine ⟨1387843557502314132507479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14803664613358017413413109 1387843557502314132507479)
                    ·
                      rfl

theorem cell23_8108447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 5].length) (baseStart_8108447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108447 prefixEnd_8108447 := by exact prefixLift 8108447
  have htrace : WordTrace (prefixWord ++ tailWord_8108447) baseStart_8108447 baseEnd_8108447 := by
    simpa [prefixWord, tailWord_8108447, baseEnd_8108447] using wordTrace_append hprefix tailTrace_8108447
  have hstable : (prefixWord ++ tailWord_8108447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108447).length < 2 ^ (prefixWord ++ tailWord_8108447).sum := by decide
  have hdescent : baseEnd_8108447 < baseStart_8108447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108477 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_8108477 : Nat := 118140960795 + 8108477 * 2 ^ 59
def prefixEnd_8108477 : Nat := 4983230072969 + 3 ^ 40 * 8108477 * 2
def baseEnd_8108477 : Nat := 1387848692308859093382433

theorem tailTrace_8108477 : CollatzResearch.WordTrace tailWord_8108477 prefixEnd_8108477 1387848692308859093382433 := by
  unfold tailWord_8108477
  simp only [CollatzResearch.WordTrace]
  refine ⟨295740452245380121465747685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197160301496920080977165123 295740452245380121465747685)
  ·
    refine ⟨55451334796008772774827691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295740452245380121465747685 55451334796008772774827691)
    ·
      refine ⟨83177002194013159162241537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55451334796008772774827691 83177002194013159162241537)
      ·
        refine ⟨62382751645509869371681153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83177002194013159162241537 62382751645509869371681153)
        ·
          refine ⟨46787063734132402028760865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62382751645509869371681153 46787063734132402028760865)
          ·
            refine ⟨35090297800599301521570649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46787063734132402028760865 35090297800599301521570649)
            ·
              refine ⟨26317723350449476141177987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35090297800599301521570649 26317723350449476141177987)
              ·
                refine ⟨39476585025674214211766981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26317723350449476141177987 39476585025674214211766981)
                ·
                  refine ⟨7401859692313915164706309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39476585025674214211766981 7401859692313915164706309)
                  ·
                    refine ⟨1387848692308859093382433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401859692313915164706309 1387848692308859093382433)
                    ·
                      rfl

theorem cell23_8108477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_8108477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108477 prefixEnd_8108477 := by exact prefixLift 8108477
  have htrace : WordTrace (prefixWord ++ tailWord_8108477) baseStart_8108477 baseEnd_8108477 := by
    simpa [prefixWord, tailWord_8108477, baseEnd_8108477] using wordTrace_append hprefix tailTrace_8108477
  have hstable : (prefixWord ++ tailWord_8108477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108477).length < 2 ^ (prefixWord ++ tailWord_8108477).sum := by decide
  have hdescent : baseEnd_8108477 < baseStart_8108477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108490 : List Nat := [3, 1, 2, 1, 2, 2, 4, 8]
def baseStart_8108490 : Nat := 118140960795 + 8108490 * 2 ^ 59
def prefixEnd_8108490 : Nat := 4983230072969 + 3 ^ 40 * 8108490 * 2
def baseEnd_8108490 : Nat := 154205657487966138121657

theorem tailTrace_8108490 : CollatzResearch.WordTrace tailWord_8108490 prefixEnd_8108490 154205657487966138121657 := by
  unfold tailWord_8108490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73935231598583256171492731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197160617596222016457313949 73935231598583256171492731)
  ·
    refine ⟨110902847397874884257239097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73935231598583256171492731 110902847397874884257239097)
    ·
      refine ⟨83177135548406163192929323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110902847397874884257239097 83177135548406163192929323)
      ·
        refine ⟨124765703322609244789393985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83177135548406163192929323 124765703322609244789393985)
        ·
          refine ⟨93574277491956933592045489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124765703322609244789393985 93574277491956933592045489)
          ·
            refine ⟨70180708118967700194034117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93574277491956933592045489 70180708118967700194034117)
            ·
              refine ⟨13158882772306443786381397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70180708118967700194034117 13158882772306443786381397)
              ·
                refine ⟨154205657487966138121657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13158882772306443786381397 154205657487966138121657)
                ·
                  rfl

theorem cell23_8108490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_8108490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108490 prefixEnd_8108490 := by exact prefixLift 8108490
  have htrace : WordTrace (prefixWord ++ tailWord_8108490) baseStart_8108490 baseEnd_8108490 := by
    simpa [prefixWord, tailWord_8108490, baseEnd_8108490] using wordTrace_append hprefix tailTrace_8108490
  have hstable : (prefixWord ++ tailWord_8108490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108490).length < 2 ^ (prefixWord ++ tailWord_8108490).sum := by decide
  have hdescent : baseEnd_8108490 < baseStart_8108490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108498 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_8108498 : Nat := 118140960795 + 8108498 * 2 ^ 59
def prefixEnd_8108498 : Nat := 4983230072969 + 3 ^ 40 * 8108498 * 2
def baseEnd_8108498 : Nat := 1387852286673440565994901

theorem tailTrace_8108498 : CollatzResearch.WordTrace tailWord_8108498 prefixEnd_8108498 1387852286673440565994901 := by
  unfold tailWord_8108498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73935304544576010513065537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197160812118869361368174765 73935304544576010513065537)
  ·
    refine ⟨55451478408432007884799153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73935304544576010513065537 55451478408432007884799153)
    ·
      refine ⟨41588608806324005913599365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55451478408432007884799153 41588608806324005913599365)
      ·
        refine ⟨7797864151185751108799881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41588608806324005913599365 7797864151185751108799881)
        ·
          refine ⟨5848398113389313331599911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797864151185751108799881 5848398113389313331599911)
          ·
            refine ⟨8772597170083969997399867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848398113389313331599911 8772597170083969997399867)
            ·
              refine ⟨13158895755125954996099801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772597170083969997399867 13158895755125954996099801)
              ·
                refine ⟨9869171816344466247074851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158895755125954996099801 9869171816344466247074851)
                ·
                  refine ⟨14803757724516699370612277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869171816344466247074851 14803757724516699370612277)
                  ·
                    refine ⟨1387852286673440565994901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14803757724516699370612277 1387852286673440565994901)
                    ·
                      rfl

theorem cell23_8108498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_8108498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108498 prefixEnd_8108498 := by exact prefixLift 8108498
  have htrace : WordTrace (prefixWord ++ tailWord_8108498) baseStart_8108498 baseEnd_8108498 := by
    simpa [prefixWord, tailWord_8108498, baseEnd_8108498] using wordTrace_append hprefix tailTrace_8108498
  have hstable : (prefixWord ++ tailWord_8108498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108498).length < 2 ^ (prefixWord ++ tailWord_8108498).sum := by decide
  have hdescent : baseEnd_8108498 < baseStart_8108498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108597 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 7]
def baseStart_8108597 : Nat := 118140960795 + 8108597 * 2 ^ 59
def prefixEnd_8108597 : Nat := 4983230072969 + 3 ^ 40 * 8108597 * 2
def baseEnd_8108597 : Nat := 462623077178346312294083

theorem tailTrace_8108597 : CollatzResearch.WordTrace tailWord_8108597 prefixEnd_8108597 462623077178346312294083 := by
  unfold tailWord_8108597
  simp only [CollatzResearch.WordTrace]
  refine ⟨295744829004945381960116045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197163219336630254640077363 295744829004945381960116045)
  ·
    refine ⟨110904310876854518235043517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295744829004945381960116045 110904310876854518235043517)
    ·
      refine ⟨41589116578820444338141319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110904310876854518235043517 41589116578820444338141319)
      ·
        refine ⟨62383674868230666507211979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41589116578820444338141319 62383674868230666507211979)
        ·
          refine ⟨93575512302345999760817969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62383674868230666507211979 93575512302345999760817969)
          ·
            refine ⟨70181634226759499820613477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93575512302345999760817969 70181634226759499820613477)
            ·
              refine ⟨13159056417517406216365027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70181634226759499820613477 13159056417517406216365027)
              ·
                refine ⟨19738584626276109324547541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13159056417517406216365027 19738584626276109324547541)
                ·
                  refine ⟨462623077178346312294083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19738584626276109324547541 462623077178346312294083)
                  ·
                    rfl

theorem cell23_8108597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_8108597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108597 prefixEnd_8108597 := by exact prefixLift 8108597
  have htrace : WordTrace (prefixWord ++ tailWord_8108597) baseStart_8108597 baseEnd_8108597 := by
    simpa [prefixWord, tailWord_8108597, baseEnd_8108597] using wordTrace_append hprefix tailTrace_8108597
  have hstable : (prefixWord ++ tailWord_8108597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108597).length < 2 ^ (prefixWord ++ tailWord_8108597).sum := by decide
  have hdescent : baseEnd_8108597 < baseStart_8108597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108607 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_8108607 : Nat := 118140960795 + 8108607 * 2 ^ 59
def prefixEnd_8108607 : Nat := 4983230072969 + 3 ^ 40 * 8108607 * 2
def baseEnd_8108607 : Nat := 4163612829411661771521701

theorem tailTrace_8108607 : CollatzResearch.WordTrace tailWord_8108607 prefixEnd_8108607 4163612829411661771521701 := by
  unfold tailWord_8108607
  simp only [CollatzResearch.WordTrace]
  refine ⟨295745193734909153667980075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197163462489939435778653383 295745193734909153667980075)
  ·
    refine ⟨443617790602363730501970113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295745193734909153667980075 443617790602363730501970113)
    ·
      refine ⟨332713342951772797876477585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443617790602363730501970113 332713342951772797876477585)
      ·
        refine ⟨249535007213829598407358189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332713342951772797876477585 249535007213829598407358189)
        ·
          refine ⟨93575627705186099402759321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249535007213829598407358189 93575627705186099402759321)
          ·
            refine ⟨70181720778889574552069491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93575627705186099402759321 70181720778889574552069491)
            ·
              refine ⟨105272581168334361828104237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70181720778889574552069491 105272581168334361828104237)
              ·
                refine ⟨39477217938125385685539089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105272581168334361828104237 39477217938125385685539089)
                ·
                  refine ⟨29607913453594039264154317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39477217938125385685539089 29607913453594039264154317)
                  ·
                    refine ⟨11102967545097764724057869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29607913453594039264154317 11102967545097764724057869)
                    ·
                      refine ⟨4163612829411661771521701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11102967545097764724057869 4163612829411661771521701)
                      ·
                        rfl

theorem cell23_8108607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_8108607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108607 prefixEnd_8108607 := by exact prefixLift 8108607
  have htrace : WordTrace (prefixWord ++ tailWord_8108607) baseStart_8108607 baseEnd_8108607 := by
    simpa [prefixWord, tailWord_8108607, baseEnd_8108607] using wordTrace_append hprefix tailTrace_8108607
  have hstable : (prefixWord ++ tailWord_8108607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108607).length < 2 ^ (prefixWord ++ tailWord_8108607).sum := by decide
  have hdescent : baseEnd_8108607 < baseStart_8108607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108612 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_8108612 : Nat := 118140960795 + 8108612 * 2 ^ 59
def prefixEnd_8108612 : Nat := 4983230072969 + 3 ^ 40 * 8108612 * 2
def baseEnd_8108612 : Nat := 4163615396814934251959179

theorem tailTrace_8108612 : CollatzResearch.WordTrace tailWord_8108612 prefixEnd_8108612 4163615396814934251959179 := by
  unfold tailWord_8108612
  simp only [CollatzResearch.WordTrace]
  refine ⟨147872688049945519760956045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197163584066594026347941393 147872688049945519760956045)
  ·
    refine ⟨55452258018729569910358517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147872688049945519760956045 55452258018729569910358517)
    ·
      refine ⟨5198649189255897179096111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55452258018729569910358517 5198649189255897179096111)
      ·
        refine ⟨7797973783883845768644167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198649189255897179096111 7797973783883845768644167)
        ·
          refine ⟨11696960675825768652966251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797973783883845768644167 11696960675825768652966251)
          ·
            refine ⟨17545441013738652979449377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696960675825768652966251 17545441013738652979449377)
            ·
              refine ⟨13159080760303989734587033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17545441013738652979449377 13159080760303989734587033)
              ·
                refine ⟨9869310570227992300940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13159080760303989734587033 9869310570227992300940275)
                ·
                  refine ⟨14803965855341988451410413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869310570227992300940275 14803965855341988451410413)
                  ·
                    refine ⟨5551487195753245669278905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14803965855341988451410413 5551487195753245669278905)
                    ·
                      refine ⟨4163615396814934251959179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5551487195753245669278905 4163615396814934251959179)
                      ·
                        rfl

theorem cell23_8108612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_8108612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108612 prefixEnd_8108612 := by exact prefixLift 8108612
  have htrace : WordTrace (prefixWord ++ tailWord_8108612) baseStart_8108612 baseEnd_8108612 := by
    simpa [prefixWord, tailWord_8108612, baseEnd_8108612] using wordTrace_append hprefix tailTrace_8108612
  have hstable : (prefixWord ++ tailWord_8108612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108612).length < 2 ^ (prefixWord ++ tailWord_8108612).sum := by decide
  have hdescent : baseEnd_8108612 < baseStart_8108612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108648 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 5]
def baseStart_8108648 : Nat := 118140960795 + 8108648 * 2 ^ 59
def prefixEnd_8108648 : Nat := 4983230072969 + 3 ^ 40 * 8108648 * 2
def baseEnd_8108648 : Nat := 462625986902055123456557

theorem tailTrace_8108648 : CollatzResearch.WordTrace tailWord_8108648 prefixEnd_8108648 462625986902055123456557 := by
  unfold tailWord_8108648
  simp only [CollatzResearch.WordTrace]
  refine ⟨147873344563880308835111299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197164459418507078446815065 147873344563880308835111299)
  ·
    refine ⟨221810016845820463252666949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147873344563880308835111299 221810016845820463252666949)
    ·
      refine ⟨41589378158591336859875053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221810016845820463252666949 41589378158591336859875053)
      ·
        refine ⟨15596016809471751322453145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41589378158591336859875053 15596016809471751322453145)
        ·
          refine ⟨11697012607103813491839859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15596016809471751322453145 11697012607103813491839859)
          ·
            refine ⟨17545518910655720237759789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697012607103813491839859 17545518910655720237759789)
            ·
              refine ⟨6579569591495895089159921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17545518910655720237759789 6579569591495895089159921)
              ·
                refine ⟨4934677193621921316869941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6579569591495895089159921 4934677193621921316869941)
                ·
                  refine ⟨462625986902055123456557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4934677193621921316869941 462625986902055123456557)
                  ·
                    rfl

theorem cell23_8108648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 5].length) (baseStart_8108648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108648 prefixEnd_8108648 := by exact prefixLift 8108648
  have htrace : WordTrace (prefixWord ++ tailWord_8108648) baseStart_8108648 baseEnd_8108648 := by
    simpa [prefixWord, tailWord_8108648, baseEnd_8108648] using wordTrace_append hprefix tailTrace_8108648
  have hstable : (prefixWord ++ tailWord_8108648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108648).length < 2 ^ (prefixWord ++ tailWord_8108648).sum := by decide
  have hdescent : baseEnd_8108648 < baseStart_8108648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108654 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8108654 : Nat := 118140960795 + 8108654 * 2 ^ 59
def prefixEnd_8108654 : Nat := 4983230072969 + 3 ^ 40 * 8108654 * 2
def baseEnd_8108654 : Nat := 4163636963002423087633985

theorem tailTrace_8108654 : CollatzResearch.WordTrace tailWord_8108654 prefixEnd_8108654 4163636963002423087633985 := by
  unfold tailWord_8108654
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968363495717360086867627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197164605310492587129960677 36968363495717360086867627)
  ·
    refine ⟨55452545243576040130301441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36968363495717360086867627 55452545243576040130301441)
    ·
      refine ⟨41589408932682030097726081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55452545243576040130301441 41589408932682030097726081)
      ·
        refine ⟨31192056699511522573294561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41589408932682030097726081 31192056699511522573294561)
        ·
          refine ⟨23394042524633641929970921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31192056699511522573294561 23394042524633641929970921)
          ·
            refine ⟨17545531893475231447478191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23394042524633641929970921 17545531893475231447478191)
            ·
              refine ⟨26318297840212847171217287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17545531893475231447478191 26318297840212847171217287)
              ·
                refine ⟨39477446760319270756825931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26318297840212847171217287 39477446760319270756825931)
                ·
                  refine ⟨59216170140478906135238897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39477446760319270756825931 59216170140478906135238897)
                  ·
                    refine ⟨44412127605359179601429173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59216170140478906135238897 44412127605359179601429173)
                    ·
                      refine ⟨4163636963002423087633985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44412127605359179601429173 4163636963002423087633985)
                      ·
                        rfl

theorem cell23_8108654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8108654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108654 prefixEnd_8108654 := by exact prefixLift 8108654
  have htrace : WordTrace (prefixWord ++ tailWord_8108654) baseStart_8108654 baseEnd_8108654 := by
    simpa [prefixWord, tailWord_8108654, baseEnd_8108654] using wordTrace_append hprefix tailTrace_8108654
  have hstable : (prefixWord ++ tailWord_8108654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108654).length < 2 ^ (prefixWord ++ tailWord_8108654).sum := by decide
  have hdescent : baseEnd_8108654 < baseStart_8108654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108667 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3]
def baseStart_8108667 : Nat := 118140960795 + 8108667 * 2 ^ 59
def prefixEnd_8108667 : Nat := 4983230072969 + 3 ^ 40 * 8108667 * 2
def baseEnd_8108667 : Nat := 4163643638250931536771425

theorem tailTrace_8108667 : CollatzResearch.WordTrace tailWord_8108667 prefixEnd_8108667 4163643638250931536771425 := by
  unfold tailWord_8108667
  simp only [CollatzResearch.WordTrace]
  refine ⟨295747382114691783915164255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197164921409794522610109503 295747382114691783915164255)
  ·
    refine ⟨443621073172037675872746383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295747382114691783915164255 443621073172037675872746383)
    ·
      refine ⟨665431609758056513809119575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443621073172037675872746383 665431609758056513809119575)
      ·
        refine ⟨998147414637084770713679363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665431609758056513809119575 998147414637084770713679363)
        ·
          refine ⟨1497221121955627156070519045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998147414637084770713679363 1497221121955627156070519045)
          ·
            refine ⟨280728960366680091763222321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1497221121955627156070519045 280728960366680091763222321)
            ·
              refine ⟨210546720275010068822416741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280728960366680091763222321 210546720275010068822416741)
              ·
                refine ⟨39477510051564387904203139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210546720275010068822416741 39477510051564387904203139)
                ·
                  refine ⟨59216265077346581856304709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39477510051564387904203139 59216265077346581856304709)
                  ·
                    refine ⟨11103049702002484098057133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59216265077346581856304709 11103049702002484098057133)
                    ·
                      refine ⟨4163643638250931536771425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103049702002484098057133 4163643638250931536771425)
                      ·
                        rfl

theorem cell23_8108667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].length) (baseStart_8108667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108667 prefixEnd_8108667 := by exact prefixLift 8108667
  have htrace : WordTrace (prefixWord ++ tailWord_8108667) baseStart_8108667 baseEnd_8108667 := by
    simpa [prefixWord, tailWord_8108667, baseEnd_8108667] using wordTrace_append hprefix tailTrace_8108667
  have hstable : (prefixWord ++ tailWord_8108667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108667).length < 2 ^ (prefixWord ++ tailWord_8108667).sum := by decide
  have hdescent : baseEnd_8108667 < baseStart_8108667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108734 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_8108734 : Nat := 118140960795 + 8108734 * 2 ^ 59
def prefixEnd_8108734 : Nat := 4983230072969 + 3 ^ 40 * 8108734 * 2
def baseEnd_8108734 : Nat := 1387892680484927591544539

theorem tailTrace_8108734 : CollatzResearch.WordTrace tailWord_8108734 prefixEnd_8108734 1387892680484927591544539 := by
  unfold tailWord_8108734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968728225681131794731657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197166550536966036238568837 36968728225681131794731657)
  ·
    refine ⟨27726546169260848846048743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36968728225681131794731657 27726546169260848846048743)
    ·
      refine ⟨41589819253891273269073115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27726546169260848846048743 41589819253891273269073115)
      ·
        refine ⟨62384728880836909903609673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41589819253891273269073115 62384728880836909903609673)
        ·
          refine ⟨46788546660627682427707255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62384728880836909903609673 46788546660627682427707255)
          ·
            refine ⟨70182819990941523641560883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46788546660627682427707255 70182819990941523641560883)
            ·
              refine ⟨105274229986412285462341325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70182819990941523641560883 105274229986412285462341325)
              ·
                refine ⟨39477836244904607048377997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105274229986412285462341325 39477836244904607048377997)
                ·
                  refine ⟨14804188591839227643141749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39477836244904607048377997 14804188591839227643141749)
                  ·
                    refine ⟨1387892680484927591544539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14804188591839227643141749 1387892680484927591544539)
                    ·
                      rfl

theorem cell23_8108734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_8108734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108734 prefixEnd_8108734 := by exact prefixLift 8108734
  have htrace : WordTrace (prefixWord ++ tailWord_8108734) baseStart_8108734 baseEnd_8108734 := by
    simpa [prefixWord, tailWord_8108734, baseEnd_8108734] using wordTrace_append hprefix tailTrace_8108734
  have hstable : (prefixWord ++ tailWord_8108734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108734).length < 2 ^ (prefixWord ++ tailWord_8108734).sum := by decide
  have hdescent : baseEnd_8108734 < baseStart_8108734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108794 : List Nat := [3, 1, 1, 1, 1, 3, 6, 7]
def baseStart_8108794 : Nat := 118140960795 + 8108794 * 2 ^ 59
def prefixEnd_8108794 : Nat := 4983230072969 + 3 ^ 40 * 8108794 * 2
def baseEnd_8108794 : Nat := 154211438899779723699383

theorem tailTrace_8108794 : CollatzResearch.WordTrace tailWord_8108794 prefixEnd_8108794 154211438899779723699383 := by
  unfold tailWord_8108794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73938003546307921151259359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197168009456821123070024957 73938003546307921151259359)
  ·
    refine ⟨110907005319461881726889039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73938003546307921151259359 110907005319461881726889039)
    ·
      refine ⟨166360507979192822590333559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110907005319461881726889039 166360507979192822590333559)
      ·
        refine ⟨249540761968789233885500339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166360507979192822590333559 249540761968789233885500339)
        ·
          refine ⟨374311142953183850828250509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249540761968789233885500339 374311142953183850828250509)
          ·
            refine ⟨140366678607443944060593941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374311142953183850828250509 140366678607443944060593941)
            ·
              refine ⟨6579688059723934877840341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140366678607443944060593941 6579688059723934877840341)
              ·
                refine ⟨154211438899779723699383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6579688059723934877840341 154211438899779723699383)
                ·
                  rfl

theorem cell23_8108794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_8108794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108794 prefixEnd_8108794 := by exact prefixLift 8108794
  have htrace : WordTrace (prefixWord ++ tailWord_8108794) baseStart_8108794 baseEnd_8108794 := by
    simpa [prefixWord, tailWord_8108794, baseEnd_8108794] using wordTrace_append hprefix tailTrace_8108794
  have hstable : (prefixWord ++ tailWord_8108794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108794).length < 2 ^ (prefixWord ++ tailWord_8108794).sum := by decide
  have hdescent : baseEnd_8108794 < baseStart_8108794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108821 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_8108821 : Nat := 118140960795 + 8108821 * 2 ^ 59
def prefixEnd_8108821 : Nat := 4983230072969 + 3 ^ 40 * 8108821 * 2
def baseEnd_8108821 : Nat := 4163722714271723934245717

theorem tailTrace_8108821 : CollatzResearch.WordTrace tailWord_8108821 prefixEnd_8108821 4163722714271723934245717 := by
  unfold tailWord_8108821
  simp only [CollatzResearch.WordTrace]
  refine ⟨295752998956133868216270317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197168665970755912144180211 295752998956133868216270317)
  ·
    refine ⟨110907374608550200581101369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295752998956133868216270317 110907374608550200581101369)
    ·
      refine ⟨83180530956412650435826027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110907374608550200581101369 83180530956412650435826027)
      ·
        refine ⟨124770796434618975653739041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83180530956412650435826027 124770796434618975653739041)
        ·
          refine ⟨93578097325964231740304281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124770796434618975653739041 93578097325964231740304281)
          ·
            refine ⟨70183572994473173805228211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93578097325964231740304281 70183572994473173805228211)
            ·
              refine ⟨105275359491709760707842317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70183572994473173805228211 105275359491709760707842317)
              ·
                refine ⟨39478259809391160265440869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105275359491709760707842317 39478259809391160265440869)
                ·
                  refine ⟨7402173714260842549770163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39478259809391160265440869 7402173714260842549770163)
                  ·
                    refine ⟨11103260571391263824655245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402173714260842549770163 11103260571391263824655245)
                    ·
                      refine ⟨4163722714271723934245717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103260571391263824655245 4163722714271723934245717)
                      ·
                        rfl

theorem cell23_8108821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_8108821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108821 prefixEnd_8108821 := by exact prefixLift 8108821
  have htrace : WordTrace (prefixWord ++ tailWord_8108821) baseStart_8108821 baseEnd_8108821 := by
    simpa [prefixWord, tailWord_8108821, baseEnd_8108821] using wordTrace_append hprefix tailTrace_8108821
  have hstable : (prefixWord ++ tailWord_8108821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108821).length < 2 ^ (prefixWord ++ tailWord_8108821).sum := by decide
  have hdescent : baseEnd_8108821 < baseStart_8108821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108842 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_8108842 : Nat := 118140960795 + 8108842 * 2 ^ 59
def prefixEnd_8108842 : Nat := 4983230072969 + 3 ^ 40 * 8108842 * 2
def baseEnd_8108842 : Nat := 4163733497365468352083121

theorem tailTrace_8108842 : CollatzResearch.WordTrace tailWord_8108842 prefixEnd_8108842 4163733497365468352083121 := by
  unfold tailWord_8108842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73938441222264447200696195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197169176592705192535189853 73938441222264447200696195)
  ·
    refine ⟨110907661833396670801044293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73938441222264447200696195 110907661833396670801044293)
    ·
      refine ⟨20795186593761875775195805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110907661833396670801044293 20795186593761875775195805)
      ·
        refine ⟨7798194972660703415698427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20795186593761875775195805 7798194972660703415698427)
        ·
          refine ⟨11697292458991055123547641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798194972660703415698427 11697292458991055123547641)
          ·
            refine ⟨8772969344243291342660731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11697292458991055123547641 8772969344243291342660731)
            ·
              refine ⟨13159454016364937013991097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772969344243291342660731 13159454016364937013991097)
              ·
                refine ⟨9869590512273702760493323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13159454016364937013991097 9869590512273702760493323)
                ·
                  refine ⟨14804385768410554140739985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869590512273702760493323 14804385768410554140739985)
                  ·
                    refine ⟨11103289326307915605554989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14804385768410554140739985 11103289326307915605554989)
                    ·
                      refine ⟨4163733497365468352083121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103289326307915605554989 4163733497365468352083121)
                      ·
                        rfl

theorem cell23_8108842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_8108842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108842 prefixEnd_8108842 := by exact prefixLift 8108842
  have htrace : WordTrace (prefixWord ++ tailWord_8108842) baseStart_8108842 baseEnd_8108842 := by
    simpa [prefixWord, tailWord_8108842, baseEnd_8108842] using wordTrace_append hprefix tailTrace_8108842
  have hstable : (prefixWord ++ tailWord_8108842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108842).length < 2 ^ (prefixWord ++ tailWord_8108842).sum := by decide
  have hdescent : baseEnd_8108842 < baseStart_8108842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108864 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_8108864 : Nat := 118140960795 + 8108864 * 2 ^ 59
def prefixEnd_8108864 : Nat := 4983230072969 + 3 ^ 40 * 8108864 * 2
def baseEnd_8108864 : Nat := 4163744793939867266008019

theorem tailTrace_8108864 : CollatzResearch.WordTrace tailWord_8108864 prefixEnd_8108864 4163744793939867266008019 := by
  unfold tailWord_8108864
  simp only [CollatzResearch.WordTrace]
  refine ⟨147877283647489043280042823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197169711529985391040057097 147877283647489043280042823)
  ·
    refine ⟨221815925471233564920064235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147877283647489043280042823 221815925471233564920064235)
    ·
      refine ⟨332723888206850347380096353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221815925471233564920064235 332723888206850347380096353)
      ·
        refine ⟨249542916155137760535072265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332723888206850347380096353 249542916155137760535072265)
        ·
          refine ⟨187157187116353320401304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249542916155137760535072265 187157187116353320401304199)
          ·
            refine ⟨280735780674529980601956299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187157187116353320401304199 280735780674529980601956299)
            ·
              refine ⟨421103671011794970902934449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280735780674529980601956299 421103671011794970902934449)
              ·
                refine ⟨315827753258846228177200837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421103671011794970902934449 315827753258846228177200837)
                ·
                  refine ⟨59217703736033667783225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315827753258846228177200837 59217703736033667783225157)
                  ·
                    refine ⟨11103319450506312709354717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59217703736033667783225157 11103319450506312709354717)
                    ·
                      refine ⟨4163744793939867266008019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103319450506312709354717 4163744793939867266008019)
                      ·
                        rfl

theorem cell23_8108864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_8108864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108864 prefixEnd_8108864 := by exact prefixLift 8108864
  have htrace : WordTrace (prefixWord ++ tailWord_8108864) baseStart_8108864 baseEnd_8108864 := by
    simpa [prefixWord, tailWord_8108864, baseEnd_8108864] using wordTrace_append hprefix tailTrace_8108864
  have hstable : (prefixWord ++ tailWord_8108864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108864).length < 2 ^ (prefixWord ++ tailWord_8108864).sum := by decide
  have hdescent : baseEnd_8108864 < baseStart_8108864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108878 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_8108878 : Nat := 118140960795 + 8108878 * 2 ^ 59
def prefixEnd_8108878 : Nat := 4983230072969 + 3 ^ 40 * 8108878 * 2
def baseEnd_8108878 : Nat := 4163751982669030211232955

theorem tailTrace_8108878 : CollatzResearch.WordTrace tailWord_8108878 prefixEnd_8108878 4163751982669030211232955 := by
  unfold tailWord_8108878
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969384739615920868886911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197170051944618244634063525 36969384739615920868886911)
  ·
    refine ⟨55454077109423881303330367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36969384739615920868886911 55454077109423881303330367)
    ·
      refine ⟨83181115664135821954995551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55454077109423881303330367 83181115664135821954995551)
      ·
        refine ⟨124771673496203732932493327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83181115664135821954995551 124771673496203732932493327)
        ·
          refine ⟨187157510244305599398739991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124771673496203732932493327 187157510244305599398739991)
          ·
            refine ⟨280736265366458399098109987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187157510244305599398739991 280736265366458399098109987)
            ·
              refine ⟨421104398049687598647164981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280736265366458399098109987 421104398049687598647164981)
              ·
                refine ⟨39478537317158212373171717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421104398049687598647164981 39478537317158212373171717)
                ·
                  refine ⟨7402225746967164819969697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39478537317158212373171717 7402225746967164819969697)
                  ·
                    refine ⟨5551669310225373614977273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7402225746967164819969697 5551669310225373614977273)
                    ·
                      refine ⟨4163751982669030211232955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5551669310225373614977273 4163751982669030211232955)
                      ·
                        rfl

theorem cell23_8108878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_8108878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108878 prefixEnd_8108878 := by exact prefixLift 8108878
  have htrace : WordTrace (prefixWord ++ tailWord_8108878) baseStart_8108878 baseEnd_8108878 := by
    simpa [prefixWord, tailWord_8108878, baseEnd_8108878] using wordTrace_append hprefix tailTrace_8108878
  have hstable : (prefixWord ++ tailWord_8108878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108878).length < 2 ^ (prefixWord ++ tailWord_8108878).sum := by decide
  have hdescent : baseEnd_8108878 < baseStart_8108878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8108924 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_8108924 : Nat := 118140960795 + 8108924 * 2 ^ 59
def prefixEnd_8108924 : Nat := 4983230072969 + 3 ^ 40 * 8108924 * 2
def baseEnd_8108924 : Nat := 4163775602779137031257743

theorem tailTrace_8108924 : CollatzResearch.WordTrace tailWord_8108924 prefixEnd_8108924 4163775602779137031257743 := by
  unfold tailWord_8108924
  simp only [CollatzResearch.WordTrace]
  refine ⟨147878377837380358403634913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197171170449840477871513217 147878377837380358403634913)
  ·
    refine ⟨110908783378035268802726185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147878377837380358403634913 110908783378035268802726185)
    ·
      refine ⟨83181587533526451602044639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110908783378035268802726185 83181587533526451602044639)
      ·
        refine ⟨124772381300289677403066959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83181587533526451602044639 124772381300289677403066959)
        ·
          refine ⟨187158571950434516104600439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124772381300289677403066959 187158571950434516104600439)
          ·
            refine ⟨280737857925651774156900659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187158571950434516104600439 280737857925651774156900659)
            ·
              refine ⟨421106786888477661235350989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280737857925651774156900659 421106786888477661235350989)
              ·
                refine ⟨157915045083179122963256621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421106786888477661235350989 157915045083179122963256621)
                ·
                  refine ⟨59218141906192171111221233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157915045083179122963256621 59218141906192171111221233)
                  ·
                    refine ⟨44413606429644128333415925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59218141906192171111221233 44413606429644128333415925)
                    ·
                      refine ⟨4163775602779137031257743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44413606429644128333415925 4163775602779137031257743)
                      ·
                        rfl

theorem cell23_8108924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_8108924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8108924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8108924 prefixEnd_8108924 := by exact prefixLift 8108924
  have htrace : WordTrace (prefixWord ++ tailWord_8108924) baseStart_8108924 baseEnd_8108924 := by
    simpa [prefixWord, tailWord_8108924, baseEnd_8108924] using wordTrace_append hprefix tailTrace_8108924
  have hstable : (prefixWord ++ tailWord_8108924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8108924).length < 2 ^ (prefixWord ++ tailWord_8108924).sum := by decide
  have hdescent : baseEnd_8108924 < baseStart_8108924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8108924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109052 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_8109052 : Nat := 118140960795 + 8109052 * 2 ^ 59
def prefixEnd_8109052 : Nat := 4983230072969 + 3 ^ 40 * 8109052 * 2
def baseEnd_8109052 : Nat := 4163841328302912530457155

theorem tailTrace_8109052 : CollatzResearch.WordTrace tailWord_8109052 prefixEnd_8109052 4163841328302912530457155 := by
  unfold tailWord_8109052
  simp only [CollatzResearch.WordTrace]
  refine ⟨147880712109148497333964705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197174282812197996445286273 147880712109148497333964705)
  ·
    refine ⟨110910534081861373000473529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147880712109148497333964705 110910534081861373000473529)
    ·
      refine ⟨83182900561396029750355147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110910534081861373000473529 83182900561396029750355147)
      ·
        refine ⟨124774350842094044625532721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83182900561396029750355147 124774350842094044625532721)
        ·
          refine ⟨93580763131570533469149541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124774350842094044625532721 93580763131570533469149541)
          ·
            refine ⟨17546393087169475025465539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93580763131570533469149541 17546393087169475025465539)
            ·
              refine ⟨26319589630754212538198309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17546393087169475025465539 26319589630754212538198309)
              ·
                refine ⟨4934923055766414850912183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26319589630754212538198309 4934923055766414850912183)
                ·
                  refine ⟨7402384583649622276368275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934923055766414850912183 7402384583649622276368275)
                  ·
                    refine ⟨11103576875474433414552413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402384583649622276368275 11103576875474433414552413)
                    ·
                      refine ⟨4163841328302912530457155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103576875474433414552413 4163841328302912530457155)
                      ·
                        rfl

theorem cell23_8109052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_8109052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109052 prefixEnd_8109052 := by exact prefixLift 8109052
  have htrace : WordTrace (prefixWord ++ tailWord_8109052) baseStart_8109052 baseEnd_8109052 := by
    simpa [prefixWord, tailWord_8109052, baseEnd_8109052] using wordTrace_append hprefix tailTrace_8109052
  have hstable : (prefixWord ++ tailWord_8109052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109052).length < 2 ^ (prefixWord ++ tailWord_8109052).sum := by decide
  have hdescent : baseEnd_8109052 < baseStart_8109052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109061 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_8109061 : Nat := 118140960795 + 8109061 * 2 ^ 59
def prefixEnd_8109061 : Nat := 4983230072969 + 3 ^ 40 * 8109061 * 2
def baseEnd_8109061 : Nat := 4163845949628802995244613

theorem tailTrace_8109061 : CollatzResearch.WordTrace tailWord_8109061 prefixEnd_8109061 4163845949628802995244613 := by
  unfold tailWord_8109061
  simp only [CollatzResearch.WordTrace]
  refine ⟨295761752475264389205007037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197174501650176259470004691 295761752475264389205007037)
  ·
    refine ⟨110910657178224145951877639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295761752475264389205007037 110910657178224145951877639)
    ·
      refine ⟨166365985767336218927816459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110910657178224145951877639 166365985767336218927816459)
      ·
        refine ⟨249548978651004328391724689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166365985767336218927816459 249548978651004328391724689)
        ·
          refine ⟨187161733988253246293793517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249548978651004328391724689 187161733988253246293793517)
          ·
            refine ⟨70185650245594967360172569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187161733988253246293793517 70185650245594967360172569)
            ·
              refine ⟨52639237684196225520129427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70185650245594967360172569 52639237684196225520129427)
              ·
                refine ⟨78958856526294338280194141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52639237684196225520129427 78958856526294338280194141)
                ·
                  refine ⟨29609571197360376855072803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78958856526294338280194141 29609571197360376855072803)
                  ·
                    refine ⟨44414356796040565282609205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29609571197360376855072803 44414356796040565282609205)
                    ·
                      refine ⟨4163845949628802995244613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44414356796040565282609205 4163845949628802995244613)
                      ·
                        rfl

theorem cell23_8109061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_8109061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109061 prefixEnd_8109061 := by exact prefixLift 8109061
  have htrace : WordTrace (prefixWord ++ tailWord_8109061) baseStart_8109061 baseEnd_8109061 := by
    simpa [prefixWord, tailWord_8109061, baseEnd_8109061] using wordTrace_append hprefix tailTrace_8109061
  have hstable : (prefixWord ++ tailWord_8109061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109061).length < 2 ^ (prefixWord ++ tailWord_8109061).sum := by decide
  have hdescent : baseEnd_8109061 < baseStart_8109061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109068 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_8109068 : Nat := 118140960795 + 8109068 * 2 ^ 59
def prefixEnd_8109068 : Nat := 4983230072969 + 3 ^ 40 * 8109068 * 2
def baseEnd_8109068 : Nat := 1387949847997794822619027

theorem tailTrace_8109068 : CollatzResearch.WordTrace tailWord_8109068 prefixEnd_8109068 1387949847997794822619027 := by
  unfold tailWord_8109068
  simp only [CollatzResearch.WordTrace]
  refine ⟨147881003893119514700255929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197174671857492686267007905 147881003893119514700255929)
  ·
    refine ⟨110910752919839636025191947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147881003893119514700255929 110910752919839636025191947)
    ·
      refine ⟨166366129379759454037787921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110910752919839636025191947 166366129379759454037787921)
      ·
        refine ⟨124774597034819590528340941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166366129379759454037787921 124774597034819590528340941)
        ·
          refine ⟨46790473888057346448127853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124774597034819590528340941 46790473888057346448127853)
          ·
            refine ⟨17546427708021504918047945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46790473888057346448127853 17546427708021504918047945)
            ·
              refine ⟨13159820781016128688535959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17546427708021504918047945 13159820781016128688535959)
              ·
                refine ⟨19739731171524193032803939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13159820781016128688535959 19739731171524193032803939)
                ·
                  refine ⟨29609596757286289549205909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19739731171524193032803939 29609596757286289549205909)
                  ·
                    refine ⟨1387949847997794822619027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29609596757286289549205909 1387949847997794822619027)
                    ·
                      rfl

theorem cell23_8109068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_8109068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109068 prefixEnd_8109068 := by exact prefixLift 8109068
  have htrace : WordTrace (prefixWord ++ tailWord_8109068) baseStart_8109068 baseEnd_8109068 := by
    simpa [prefixWord, tailWord_8109068, baseEnd_8109068] using wordTrace_append hprefix tailTrace_8109068
  have hstable : (prefixWord ++ tailWord_8109068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109068).length < 2 ^ (prefixWord ++ tailWord_8109068).sum := by decide
  have hdescent : baseEnd_8109068 < baseStart_8109068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109092 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_8109092 : Nat := 118140960795 + 8109092 * 2 ^ 59
def prefixEnd_8109092 : Nat := 4983230072969 + 3 ^ 40 * 8109092 * 2
def baseEnd_8109092 : Nat := 4163861867529092373956971

theorem tailTrace_8109092 : CollatzResearch.WordTrace tailWord_8109092 prefixEnd_8109092 4163861867529092373956971 := by
  unfold tailWord_8109092
  simp only [CollatzResearch.WordTrace]
  refine ⟨147881441569076040749692765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197175255425434720999590353 147881441569076040749692765)
  ·
    refine ⟨55455540588403515281134787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147881441569076040749692765 55455540588403515281134787)
    ·
      refine ⟨83183310882605272921702181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55455540588403515281134787 83183310882605272921702181)
      ·
        refine ⟨15596870790488488672819159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83183310882605272921702181 15596870790488488672819159)
        ·
          refine ⟨23395306185732733009228739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15596870790488488672819159 23395306185732733009228739)
          ·
            refine ⟨35092959278599099513843109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23395306185732733009228739 35092959278599099513843109)
            ·
              refine ⟨6579929864737331158845583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35092959278599099513843109 6579929864737331158845583)
              ·
                refine ⟨9869894797105996738268375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579929864737331158845583 9869894797105996738268375)
                ·
                  refine ⟨14804842195658995107402563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869894797105996738268375 14804842195658995107402563)
                  ·
                    refine ⟨22207263293488492661103845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14804842195658995107402563 22207263293488492661103845)
                    ·
                      refine ⟨4163861867529092373956971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22207263293488492661103845 4163861867529092373956971)
                      ·
                        rfl

theorem cell23_8109092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_8109092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109092 prefixEnd_8109092 := by exact prefixLift 8109092
  have htrace : WordTrace (prefixWord ++ tailWord_8109092) baseStart_8109092 baseEnd_8109092 := by
    simpa [prefixWord, tailWord_8109092, baseEnd_8109092] using wordTrace_append hprefix tailTrace_8109092
  have hstable : (prefixWord ++ tailWord_8109092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109092).length < 2 ^ (prefixWord ++ tailWord_8109092).sum := by decide
  have hdescent : baseEnd_8109092 < baseStart_8109092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109098 : List Nat := [3, 1, 4, 1, 3, 1, 10]
def baseStart_8109098 : Nat := 118140960795 + 8109098 * 2 ^ 59
def prefixEnd_8109098 : Nat := 4983230072969 + 3 ^ 40 * 8109098 * 2
def baseEnd_8109098 : Nat := 51405740103864436425703

theorem tailTrace_8109098 : CollatzResearch.WordTrace tailWord_8109098 prefixEnd_8109098 51405740103864436425703 := by
  unfold tailWord_8109098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73940775494032586131025987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197175401317420229682735965 73940775494032586131025987)
  ·
    refine ⟨110911163241048879196538981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73940775494032586131025987 110911163241048879196538981)
    ·
      refine ⟨20795843107696664849351059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110911163241048879196538981 20795843107696664849351059)
      ·
        refine ⟨31193764661544997274026589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20795843107696664849351059 31193764661544997274026589)
        ·
          refine ⟨11697661748079373977759971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31193764661544997274026589 11697661748079373977759971)
          ·
            refine ⟨17546492622119060966639957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697661748079373977759971 17546492622119060966639957)
            ·
              refine ⟨51405740103864436425703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17546492622119060966639957 51405740103864436425703)
              ·
                rfl

theorem cell23_8109098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 10].length) (baseStart_8109098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109098 prefixEnd_8109098 := by exact prefixLift 8109098
  have htrace : WordTrace (prefixWord ++ tailWord_8109098) baseStart_8109098 baseEnd_8109098 := by
    simpa [prefixWord, tailWord_8109098, baseEnd_8109098] using wordTrace_append hprefix tailTrace_8109098
  have hstable : (prefixWord ++ tailWord_8109098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109098).length < 2 ^ (prefixWord ++ tailWord_8109098).sum := by decide
  have hdescent : baseEnd_8109098 < baseStart_8109098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109125 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_8109125 : Nat := 118140960795 + 8109125 * 2 ^ 59
def prefixEnd_8109125 : Nat := 4983230072969 + 3 ^ 40 * 8109125 * 2
def baseEnd_8109125 : Nat := 4163878812390690744844319

theorem tailTrace_8109125 : CollatzResearch.WordTrace tailWord_8109125 prefixEnd_8109125 4163878812390690744844319 := by
  unfold tailWord_8109125
  simp only [CollatzResearch.WordTrace]
  refine ⟨295764086747032528135336829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197176057831355018756891219 295764086747032528135336829)
  ·
    refine ⟨110911532530137198050751311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295764086747032528135336829 110911532530137198050751311)
    ·
      refine ⟨166367298795205797076126967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110911532530137198050751311 166367298795205797076126967)
      ·
        refine ⟨249550948192808695614190451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166367298795205797076126967 249550948192808695614190451)
        ·
          refine ⟨374326422289213043421285677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249550948192808695614190451 374326422289213043421285677)
          ·
            refine ⟨140372408358454891282982129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374326422289213043421285677 140372408358454891282982129)
            ·
              refine ⟨105279306268841168462236597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140372408358454891282982129 105279306268841168462236597)
              ·
                refine ⟨9869934962703859543334681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105279306268841168462236597 9869934962703859543334681)
                ·
                  refine ⟨7402451222027894657501011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869934962703859543334681 7402451222027894657501011)
                  ·
                    refine ⟨11103676833041841986251517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402451222027894657501011 11103676833041841986251517)
                    ·
                      refine ⟨4163878812390690744844319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103676833041841986251517 4163878812390690744844319)
                      ·
                        rfl

theorem cell23_8109125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_8109125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109125 prefixEnd_8109125 := by exact prefixLift 8109125
  have htrace : WordTrace (prefixWord ++ tailWord_8109125) baseStart_8109125 baseEnd_8109125 := by
    simpa [prefixWord, tailWord_8109125, baseEnd_8109125] using wordTrace_append hprefix tailTrace_8109125
  have hstable : (prefixWord ++ tailWord_8109125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109125).length < 2 ^ (prefixWord ++ tailWord_8109125).sum := by decide
  have hdescent : baseEnd_8109125 < baseStart_8109125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109138 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_8109138 : Nat := 118140960795 + 8109138 * 2 ^ 59
def prefixEnd_8109138 : Nat := 4983230072969 + 3 ^ 40 * 8109138 * 2
def baseEnd_8109138 : Nat := 4163885487639199193981759

theorem tailTrace_8109138 : CollatzResearch.WordTrace tailWord_8109138 prefixEnd_8109138 4163885487639199193981759 := by
  unfold tailWord_8109138
  simp only [CollatzResearch.WordTrace]
  refine ⟨73941140223996357838890017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197176373930656954237040045 73941140223996357838890017)
  ·
    refine ⟨55455855167997268379167513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73941140223996357838890017 55455855167997268379167513)
    ·
      refine ⟨41591891375997951284375635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55455855167997268379167513 41591891375997951284375635)
      ·
        refine ⟨62387837063996926926563453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41591891375997951284375635 62387837063996926926563453)
        ·
          refine ⟨23395438898998847597461295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62387837063996926926563453 23395438898998847597461295)
          ·
            refine ⟨35093158348498271396191943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23395438898998847597461295 35093158348498271396191943)
            ·
              refine ⟨52639737522747407094287915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35093158348498271396191943 52639737522747407094287915)
              ·
                refine ⟨78959606284121110641431873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52639737522747407094287915 78959606284121110641431873)
                ·
                  refine ⟨59219704713090832981073905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78959606284121110641431873 59219704713090832981073905)
                  ·
                    refine ⟨44414778534818124735805429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59219704713090832981073905 44414778534818124735805429)
                    ·
                      refine ⟨4163885487639199193981759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44414778534818124735805429 4163885487639199193981759)
                      ·
                        rfl

theorem cell23_8109138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_8109138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109138 prefixEnd_8109138 := by exact prefixLift 8109138
  have htrace : WordTrace (prefixWord ++ tailWord_8109138) baseStart_8109138 baseEnd_8109138 := by
    simpa [prefixWord, tailWord_8109138, baseEnd_8109138] using wordTrace_append hprefix tailTrace_8109138
  have hstable : (prefixWord ++ tailWord_8109138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109138).length < 2 ^ (prefixWord ++ tailWord_8109138).sum := by decide
  have hdescent : baseEnd_8109138 < baseStart_8109138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109168 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_8109168 : Nat := 118140960795 + 8109168 * 2 ^ 59
def prefixEnd_8109168 : Nat := 4983230072969 + 3 ^ 40 * 8109168 * 2
def baseEnd_8109168 : Nat := 4163900892058834076606621

theorem tailTrace_8109168 : CollatzResearch.WordTrace tailWord_8109168 prefixEnd_8109168 4163900892058834076606621 := by
  unfold tailWord_8109168
  simp only [CollatzResearch.WordTrace]
  refine ⟨147882827542938373239576079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197177103390584497652768105 147882827542938373239576079)
  ·
    refine ⟨221824241314407559859364119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147882827542938373239576079 221824241314407559859364119)
    ·
      refine ⟨332736361971611339789046179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221824241314407559859364119 332736361971611339789046179)
      ·
        refine ⟨499104542957417009683569269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332736361971611339789046179 499104542957417009683569269)
        ·
          refine ⟨46791050902257844657834619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 499104542957417009683569269 46791050902257844657834619)
          ·
            refine ⟨70186576353386766986751929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46791050902257844657834619 70186576353386766986751929)
            ·
              refine ⟨52639932265040075240063947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70186576353386766986751929 52639932265040075240063947)
              ·
                refine ⟨78959898397560112860095921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52639932265040075240063947 78959898397560112860095921)
                ·
                  refine ⟨59219923798170084645071941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78959898397560112860095921 59219923798170084645071941)
                  ·
                    refine ⟨11103735712156890870950989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59219923798170084645071941 11103735712156890870950989)
                    ·
                      refine ⟨4163900892058834076606621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11103735712156890870950989 4163900892058834076606621)
                      ·
                        rfl

theorem cell23_8109168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_8109168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109168 prefixEnd_8109168 := by exact prefixLift 8109168
  have htrace : WordTrace (prefixWord ++ tailWord_8109168) baseStart_8109168 baseEnd_8109168 := by
    simpa [prefixWord, tailWord_8109168, baseEnd_8109168] using wordTrace_append hprefix tailTrace_8109168
  have hstable : (prefixWord ++ tailWord_8109168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109168).length < 2 ^ (prefixWord ++ tailWord_8109168).sum := by decide
  have hdescent : baseEnd_8109168 < baseStart_8109168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109316 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_8109316 : Nat := 118140960795 + 8109316 * 2 ^ 59
def prefixEnd_8109316 : Nat := 4983230072969 + 3 ^ 40 * 8109316 * 2
def baseEnd_8109316 : Nat := 1387992295731899832518647

theorem tailTrace_8109316 : CollatzResearch.WordTrace tailWord_8109316 prefixEnd_8109316 1387992295731899832518647 := by
  unfold tailWord_8109316
  simp only [CollatzResearch.WordTrace]
  refine ⟨147885526544670283877769901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197180702059560378503693201 147885526544670283877769901)
  ·
    refine ⟨55457072454251356454163713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147885526544670283877769901 55457072454251356454163713)
    ·
      refine ⟨41592804340688517340622785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55457072454251356454163713 41592804340688517340622785)
      ·
        refine ⟨31194603255516388005467089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41592804340688517340622785 31194603255516388005467089)
        ·
          refine ⟨23395952441637291004100317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31194603255516388005467089 23395952441637291004100317)
          ·
            refine ⟨8773482165613984126537619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23395952441637291004100317 8773482165613984126537619)
            ·
              refine ⟨13160223248420976189806429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773482165613984126537619 13160223248420976189806429)
              ·
                refine ⟨4935083718157866071177411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160223248420976189806429 4935083718157866071177411)
                ·
                  refine ⟨7402625577236799106766117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935083718157866071177411 7402625577236799106766117)
                  ·
                    refine ⟨1387992295731899832518647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402625577236799106766117 1387992295731899832518647)
                    ·
                      rfl

theorem cell23_8109316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_8109316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109316 prefixEnd_8109316 := by exact prefixLift 8109316
  have htrace : WordTrace (prefixWord ++ tailWord_8109316) baseStart_8109316 baseEnd_8109316 := by
    simpa [prefixWord, tailWord_8109316, baseEnd_8109316] using wordTrace_append hprefix tailTrace_8109316
  have hstable : (prefixWord ++ tailWord_8109316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109316).length < 2 ^ (prefixWord ++ tailWord_8109316).sum := by decide
  have hdescent : baseEnd_8109316 < baseStart_8109316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109328 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_8109328 : Nat := 118140960795 + 8109328 * 2 ^ 59
def prefixEnd_8109328 : Nat := 4983230072969 + 3 ^ 40 * 8109328 * 2
def baseEnd_8109328 : Nat := 4163983048963553450605885

theorem tailTrace_8109328 : CollatzResearch.WordTrace tailWord_8109328 prefixEnd_8109328 4163983048963553450605885 := by
  unfold tailWord_8109328
  simp only [CollatzResearch.WordTrace]
  refine ⟨147885745382648546902488319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197180993843531395869984425 147885745382648546902488319)
  ·
    refine ⟨221828618073972820353732479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147885745382648546902488319 221828618073972820353732479)
    ·
      refine ⟨332742927110959230530598719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221828618073972820353732479 332742927110959230530598719)
      ·
        refine ⟨499114390666438845795898079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332742927110959230530598719 499114390666438845795898079)
        ·
          refine ⟨748671585999658268693847119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499114390666438845795898079 748671585999658268693847119)
          ·
            refine ⟨1123007378999487403040770679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748671585999658268693847119 1123007378999487403040770679)
            ·
              refine ⟨1684511068499231104561156019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123007378999487403040770679 1684511068499231104561156019)
              ·
                refine ⟨2526766602748846656841734029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684511068499231104561156019 2526766602748846656841734029)
                ·
                  refine ⟨947537476030817496315650261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2526766602748846656841734029 947537476030817496315650261)
                  ·
                    refine ⟨22207909594472285069898053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 947537476030817496315650261 22207909594472285069898053)
                    ·
                      refine ⟨4163983048963553450605885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22207909594472285069898053 4163983048963553450605885)
                      ·
                        rfl

theorem cell23_8109328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_8109328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109328 prefixEnd_8109328 := by exact prefixLift 8109328
  have htrace : WordTrace (prefixWord ++ tailWord_8109328) baseStart_8109328 baseEnd_8109328 := by
    simpa [prefixWord, tailWord_8109328, baseEnd_8109328] using wordTrace_append hprefix tailTrace_8109328
  have hstable : (prefixWord ++ tailWord_8109328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109328).length < 2 ^ (prefixWord ++ tailWord_8109328).sum := by decide
  have hdescent : baseEnd_8109328 < baseStart_8109328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109345 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_8109345 : Nat := 118140960795 + 8109345 * 2 ^ 59
def prefixEnd_8109345 : Nat := 4983230072969 + 3 ^ 40 * 8109345 * 2
def baseEnd_8109345 : Nat := 4163991778134679884093307

theorem tailTrace_8109345 : CollatzResearch.WordTrace tailWord_8109345 prefixEnd_8109345 4163991778134679884093307 := by
  unfold tailWord_8109345
  simp only [CollatzResearch.WordTrace]
  refine ⟨295772110806235505708345489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197181407204157003805563659 295772110806235505708345489)
  ·
    refine ⟨221829083104676629281259117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295772110806235505708345489 221829083104676629281259117)
    ·
      refine ⟨83185906164253735980472169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221829083104676629281259117 83185906164253735980472169)
      ·
        refine ⟨62389429623190301985354127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83185906164253735980472169 62389429623190301985354127)
        ·
          refine ⟨93584144434785452978031191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62389429623190301985354127 93584144434785452978031191)
          ·
            refine ⟨140376216652178179467046787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93584144434785452978031191 140376216652178179467046787)
            ·
              refine ⟨210564324978267269200570181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140376216652178179467046787 210564324978267269200570181)
              ·
                refine ⟨39480810933425112975106909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210564324978267269200570181 39480810933425112975106909)
                ·
                  refine ⟨14805304100034417365665091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39480810933425112975106909 14805304100034417365665091)
                  ·
                    refine ⟨22207956150051626048497637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14805304100034417365665091 22207956150051626048497637)
                    ·
                      refine ⟨4163991778134679884093307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22207956150051626048497637 4163991778134679884093307)
                      ·
                        rfl

theorem cell23_8109345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_8109345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109345 prefixEnd_8109345 := by exact prefixLift 8109345
  have htrace : WordTrace (prefixWord ++ tailWord_8109345) baseStart_8109345 baseEnd_8109345 := by
    simpa [prefixWord, tailWord_8109345, baseEnd_8109345] using wordTrace_append hprefix tailTrace_8109345
  have hstable : (prefixWord ++ tailWord_8109345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109345).length < 2 ^ (prefixWord ++ tailWord_8109345).sum := by decide
  have hdescent : baseEnd_8109345 < baseStart_8109345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109346 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_8109346 : Nat := 118140960795 + 8109346 * 2 ^ 59
def prefixEnd_8109346 : Nat := 4983230072969 + 3 ^ 40 * 8109346 * 2
def baseEnd_8109346 : Nat := 462665810179481597797867

theorem tailTrace_8109346 : CollatzResearch.WordTrace tailWord_8109346 prefixEnd_8109346 462665810179481597797867 := by
  unfold tailWord_8109346
  simp only [CollatzResearch.WordTrace]
  refine ⟨73943036819807970719782973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197181431519487921919421261 73943036819807970719782973)
  ·
    refine ⟨27728638807427989019918615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73943036819807970719782973 27728638807427989019918615)
    ·
      refine ⟨41592958211141983529877923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27728638807427989019918615 41592958211141983529877923)
      ·
        refine ⟨62389437316712975294816885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41592958211141983529877923 62389437316712975294816885)
        ·
          refine ⟨5849009748441841433889083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62389437316712975294816885 5849009748441841433889083)
          ·
            refine ⟨8773514622662762150833625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849009748441841433889083 8773514622662762150833625)
            ·
              refine ⟨6580135966997071613125219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8773514622662762150833625 6580135966997071613125219)
              ·
                refine ⟨9870203950495607419687829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580135966997071613125219 9870203950495607419687829)
                ·
                  refine ⟨462665810179481597797867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9870203950495607419687829 462665810179481597797867)
                  ·
                    rfl

theorem cell23_8109346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_8109346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109346 prefixEnd_8109346 := by exact prefixLift 8109346
  have htrace : WordTrace (prefixWord ++ tailWord_8109346) baseStart_8109346 baseEnd_8109346 := by
    simpa [prefixWord, tailWord_8109346, baseEnd_8109346] using wordTrace_append hprefix tailTrace_8109346
  have hstable : (prefixWord ++ tailWord_8109346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109346).length < 2 ^ (prefixWord ++ tailWord_8109346).sum := by decide
  have hdescent : baseEnd_8109346 < baseStart_8109346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109362 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_8109362 : Nat := 118140960795 + 8109362 * 2 ^ 59
def prefixEnd_8109362 : Nat := 4983230072969 + 3 ^ 40 * 8109362 * 2
def baseEnd_8109362 : Nat := 4164000507305806317580729

theorem tailTrace_8109362 : CollatzResearch.WordTrace tailWord_8109362 prefixEnd_8109362 4164000507305806317580729 := by
  unfold tailWord_8109362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73943182711793479402928585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197181820564782611741142893 73943182711793479402928585)
  ·
    refine ⟨55457387033845109552196439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73943182711793479402928585 55457387033845109552196439)
    ·
      refine ⟨83186080550767664328294659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55457387033845109552196439 83186080550767664328294659)
      ·
        refine ⟨124779120826151496492441989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83186080550767664328294659 124779120826151496492441989)
        ·
          refine ⟨23396085154903405592332873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124779120826151496492441989 23396085154903405592332873)
          ·
            refine ⟨17547063866177554194249655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23396085154903405592332873 17547063866177554194249655)
            ·
              refine ⟨26320595799266331291374483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17547063866177554194249655 26320595799266331291374483)
              ·
                refine ⟨39480893698899496937061725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26320595799266331291374483 39480893698899496937061725)
                ·
                  refine ⟨14805335137087311351398147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39480893698899496937061725 14805335137087311351398147)
                  ·
                    refine ⟨22208002705630967027097221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14805335137087311351398147 22208002705630967027097221)
                    ·
                      refine ⟨4164000507305806317580729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22208002705630967027097221 4164000507305806317580729)
                      ·
                        rfl

theorem cell23_8109362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_8109362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109362 prefixEnd_8109362 := by exact prefixLift 8109362
  have htrace : WordTrace (prefixWord ++ tailWord_8109362) baseStart_8109362 baseEnd_8109362 := by
    simpa [prefixWord, tailWord_8109362, baseEnd_8109362] using wordTrace_append hprefix tailTrace_8109362
  have hstable : (prefixWord ++ tailWord_8109362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109362).length < 2 ^ (prefixWord ++ tailWord_8109362).sum := by decide
  have hdescent : baseEnd_8109362 < baseStart_8109362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109375 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_8109375 : Nat := 118140960795 + 8109375 * 2 ^ 59
def prefixEnd_8109375 : Nat := 4983230072969 + 3 ^ 40 * 8109375 * 2
def baseEnd_8109375 : Nat := 4164007182554314766718169

theorem tailTrace_8109375 : CollatzResearch.WordTrace tailWord_8109375 prefixEnd_8109375 4164007182554314766718169 := by
  unfold tailWord_8109375
  simp only [CollatzResearch.WordTrace]
  refine ⟨295773204996126820831937579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197182136664084547221291719 295773204996126820831937579)
  ·
    refine ⟨443659807494190231247906369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295773204996126820831937579 443659807494190231247906369)
    ·
      refine ⟨332744855620642673435929777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443659807494190231247906369 332744855620642673435929777)
      ·
        refine ⟨249558641715482005076947333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332744855620642673435929777 249558641715482005076947333)
        ·
          refine ⟨46792245321652875951927625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249558641715482005076947333 46792245321652875951927625)
          ·
            refine ⟨35094183991239656963945719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46792245321652875951927625 35094183991239656963945719)
            ·
              refine ⟨52641275986859485445918579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35094183991239656963945719 52641275986859485445918579)
              ·
                refine ⟨78961913980289228168877869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52641275986859485445918579 78961913980289228168877869)
                ·
                  refine ⟨29610717742608460563329201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78961913980289228168877869 29610717742608460563329201)
                  ·
                    refine ⟨22208038306956345422496901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29610717742608460563329201 22208038306956345422496901)
                    ·
                      refine ⟨4164007182554314766718169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22208038306956345422496901 4164007182554314766718169)
                      ·
                        rfl

theorem cell23_8109375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_8109375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109375 prefixEnd_8109375 := by exact prefixLift 8109375
  have htrace : WordTrace (prefixWord ++ tailWord_8109375) baseStart_8109375 baseEnd_8109375 := by
    simpa [prefixWord, tailWord_8109375, baseEnd_8109375] using wordTrace_append hprefix tailTrace_8109375
  have hstable : (prefixWord ++ tailWord_8109375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109375).length < 2 ^ (prefixWord ++ tailWord_8109375).sum := by decide
  have hdescent : baseEnd_8109375 < baseStart_8109375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109395 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3]
def baseStart_8109395 : Nat := 118140960795 + 8109395 * 2 ^ 59
def prefixEnd_8109395 : Nat := 4983230072969 + 3 ^ 40 * 8109395 * 2
def baseEnd_8109395 : Nat := 4164017452167404688468077

theorem tailTrace_8109395 : CollatzResearch.WordTrace tailWord_8109395 prefixEnd_8109395 4164017452167404688468077 := by
  unfold tailWord_8109395
  simp only [CollatzResearch.WordTrace]
  refine ⟨295773934456054364247665639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197182622970702909498443759 295773934456054364247665639)
  ·
    refine ⟨443660901684081546371498459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295773934456054364247665639 443660901684081546371498459)
    ·
      refine ⟨665491352526122319557247689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443660901684081546371498459 665491352526122319557247689)
      ·
        refine ⟨499118514394591739667935767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665491352526122319557247689 499118514394591739667935767)
        ·
          refine ⟨748677771591887609501903651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499118514394591739667935767 748677771591887609501903651)
          ·
            refine ⟨1123016657387831414252855477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748677771591887609501903651 1123016657387831414252855477)
            ·
              refine ⟨105282811630109195086205201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1123016657387831414252855477 105282811630109195086205201)
              ·
                refine ⟨78962108722581896314653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105282811630109195086205201 78962108722581896314653901)
                ·
                  refine ⟨29610790770968211117995213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78962108722581896314653901 29610790770968211117995213)
                  ·
                    refine ⟨11104046539113079169248205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29610790770968211117995213 11104046539113079169248205)
                    ·
                      refine ⟨4164017452167404688468077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104046539113079169248205 4164017452167404688468077)
                      ·
                        rfl

theorem cell23_8109395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_8109395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109395 prefixEnd_8109395 := by exact prefixLift 8109395
  have htrace : WordTrace (prefixWord ++ tailWord_8109395) baseStart_8109395 baseEnd_8109395 := by
    simpa [prefixWord, tailWord_8109395, baseEnd_8109395] using wordTrace_append hprefix tailTrace_8109395
  have hstable : (prefixWord ++ tailWord_8109395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109395).length < 2 ^ (prefixWord ++ tailWord_8109395).sum := by decide
  have hdescent : baseEnd_8109395 < baseStart_8109395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109412 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_8109412 : Nat := 118140960795 + 8109412 * 2 ^ 59
def prefixEnd_8109412 : Nat := 4983230072969 + 3 ^ 40 * 8109412 * 2
def baseEnd_8109412 : Nat := 4164026181338531121955499

theorem tailTrace_8109412 : CollatzResearch.WordTrace tailWord_8109412 prefixEnd_8109412 4164026181338531121955499 := by
  unfold tailWord_8109412
  simp only [CollatzResearch.WordTrace]
  refine ⟨147887277248496388075517245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197183036331328517434022993 147887277248496388075517245)
  ·
    refine ⟨55457728968186145528318967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147887277248496388075517245 55457728968186145528318967)
    ·
      refine ⟨83186593452279218292478451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55457728968186145528318967 83186593452279218292478451)
      ·
        refine ⟨124779890178418827438717677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83186593452279218292478451 124779890178418827438717677)
        ·
          refine ⟨46792458816907060289519129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124779890178418827438717677 46792458816907060289519129)
          ·
            refine ⟨35094344112680295217139347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46792458816907060289519129 35094344112680295217139347)
            ·
              refine ⟨52641516169020442825709021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35094344112680295217139347 52641516169020442825709021)
              ·
                refine ⟨19740568563382666059640883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52641516169020442825709021 19740568563382666059640883)
                ·
                  refine ⟨29610852845073999089461325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19740568563382666059640883 29610852845073999089461325)
                  ·
                    refine ⟨11104069816902749658547997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29610852845073999089461325 11104069816902749658547997)
                    ·
                      refine ⟨4164026181338531121955499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104069816902749658547997 4164026181338531121955499)
                      ·
                        rfl

theorem cell23_8109412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_8109412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109412 prefixEnd_8109412 := by exact prefixLift 8109412
  have htrace : WordTrace (prefixWord ++ tailWord_8109412) baseStart_8109412 baseEnd_8109412 := by
    simpa [prefixWord, tailWord_8109412, baseEnd_8109412] using wordTrace_append hprefix tailTrace_8109412
  have hstable : (prefixWord ++ tailWord_8109412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109412).length < 2 ^ (prefixWord ++ tailWord_8109412).sum := by decide
  have hdescent : baseEnd_8109412 < baseStart_8109412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109445 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_8109445 : Nat := 118140960795 + 8109445 * 2 ^ 59
def prefixEnd_8109445 : Nat := 4983230072969 + 3 ^ 40 * 8109445 * 2
def baseEnd_8109445 : Nat := 1388014375400043164280949

theorem tailTrace_8109445 : CollatzResearch.WordTrace tailWord_8109445 prefixEnd_8109445 1388014375400043164280949 := by
  unfold tailWord_8109445
  simp only [CollatzResearch.WordTrace]
  refine ⟨295775758105873222786985789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197183838737248815191323859 295775758105873222786985789)
  ·
    refine ⟨110915909289702458545119671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295775758105873222786985789 110915909289702458545119671)
    ·
      refine ⟨166373863934553687817679507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110915909289702458545119671 166373863934553687817679507)
      ·
        refine ⟨249560795901830531726519261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166373863934553687817679507 249560795901830531726519261)
        ·
          refine ⟨93585298463186449397444723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249560795901830531726519261 93585298463186449397444723)
          ·
            refine ⟨140377947694779674096167085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93585298463186449397444723 140377947694779674096167085)
            ·
              refine ⟨52641730385542377786062657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140377947694779674096167085 52641730385542377786062657)
              ·
                refine ⟨39481297789156783339546993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52641730385542377786062657 39481297789156783339546993)
                ·
                  refine ⟨29610973341867587504660245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39481297789156783339546993 29610973341867587504660245)
                  ·
                    refine ⟨1388014375400043164280949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29610973341867587504660245 1388014375400043164280949)
                    ·
                      rfl

theorem cell23_8109445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_8109445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109445 prefixEnd_8109445 := by exact prefixLift 8109445
  have htrace : WordTrace (prefixWord ++ tailWord_8109445) baseStart_8109445 baseEnd_8109445 := by
    simpa [prefixWord, tailWord_8109445, baseEnd_8109445] using wordTrace_append hprefix tailTrace_8109445
  have hstable : (prefixWord ++ tailWord_8109445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109445).length < 2 ^ (prefixWord ++ tailWord_8109445).sum := by decide
  have hdescent : baseEnd_8109445 < baseStart_8109445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109475 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 7]
def baseStart_8109475 : Nat := 118140960795 + 8109475 * 2 ^ 59
def prefixEnd_8109475 : Nat := 4983230072969 + 3 ^ 40 * 8109475 * 2
def baseEnd_8109475 : Nat := 462673170068862708385301

theorem tailTrace_8109475 : CollatzResearch.WordTrace tailWord_8109475 prefixEnd_8109475 462673170068862708385301 := by
  unfold tailWord_8109475
  simp only [CollatzResearch.WordTrace]
  refine ⟨295776852295764537910577879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197184568197176358607051919 295776852295764537910577879)
  ·
    refine ⟨443665278443646806865866819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295776852295764537910577879 443665278443646806865866819)
    ·
      refine ⟨665497917665470210298800229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443665278443646806865866819 665497917665470210298800229)
      ·
        refine ⟨124780859562275664431025043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665497917665470210298800229 124780859562275664431025043)
        ·
          refine ⟨187171289343413496646537565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124780859562275664431025043 187171289343413496646537565)
          ·
            refine ⟨70189233503780061242451587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187171289343413496646537565 70189233503780061242451587)
            ·
              refine ⟨105283850255670091863677381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70189233503780061242451587 105283850255670091863677381)
              ·
                refine ⟨19740721922938142224439509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105283850255670091863677381 19740721922938142224439509)
                ·
                  refine ⟨462673170068862708385301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19740721922938142224439509 462673170068862708385301)
                  ·
                    rfl

theorem cell23_8109475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 7].length) (baseStart_8109475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109475 prefixEnd_8109475 := by exact prefixLift 8109475
  have htrace : WordTrace (prefixWord ++ tailWord_8109475) baseStart_8109475 baseEnd_8109475 := by
    simpa [prefixWord, tailWord_8109475, baseEnd_8109475] using wordTrace_append hprefix tailTrace_8109475
  have hstable : (prefixWord ++ tailWord_8109475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109475).length < 2 ^ (prefixWord ++ tailWord_8109475).sum := by decide
  have hdescent : baseEnd_8109475 < baseStart_8109475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109515 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_8109515 : Nat := 118140960795 + 8109515 * 2 ^ 59
def prefixEnd_8109515 : Nat := 4983230072969 + 3 ^ 40 * 8109515 * 2
def baseEnd_8109515 : Nat := 4164079069845944218967525

theorem tailTrace_8109515 : CollatzResearch.WordTrace tailWord_8109515 prefixEnd_8109515 4164079069845944218967525 := by
  unfold tailWord_8109515
  simp only [CollatzResearch.WordTrace]
  refine ⟨295778311215619624742033999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197185540810413083161355999 295778311215619624742033999)
  ·
    refine ⟨443667466823429437113050999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295778311215619624742033999 443667466823429437113050999)
    ·
      refine ⟨665501200235144155669576499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443667466823429437113050999 665501200235144155669576499)
      ·
        refine ⟨998251800352716233504364749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665501200235144155669576499 998251800352716233504364749)
        ·
          refine ⟨374344425132268587564136781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 998251800352716233504364749 374344425132268587564136781)
          ·
            refine ⟨140379159424600720336551293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374344425132268587564136781 140379159424600720336551293)
            ·
              refine ⟨52642184784225270126206735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140379159424600720336551293 52642184784225270126206735)
              ·
                refine ⟨78963277176337905189310103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52642184784225270126206735 78963277176337905189310103)
                ·
                  refine ⟨118444915764506857783965155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78963277176337905189310103 118444915764506857783965155)
                  ·
                    refine ⟨177667373646760286675947733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118444915764506857783965155 177667373646760286675947733)
                    ·
                      refine ⟨4164079069845944218967525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177667373646760286675947733 4164079069845944218967525)
                      ·
                        rfl

theorem cell23_8109515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_8109515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109515 prefixEnd_8109515 := by exact prefixLift 8109515
  have htrace : WordTrace (prefixWord ++ tailWord_8109515) baseStart_8109515 baseEnd_8109515 := by
    simpa [prefixWord, tailWord_8109515, baseEnd_8109515] using wordTrace_append hprefix tailTrace_8109515
  have hstable : (prefixWord ++ tailWord_8109515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109515).length < 2 ^ (prefixWord ++ tailWord_8109515).sum := by decide
  have hdescent : baseEnd_8109515 < baseStart_8109515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109539 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 2, 5]
def baseStart_8109539 : Nat := 118140960795 + 8109539 * 2 ^ 59
def prefixEnd_8109539 : Nat := 4983230072969 + 3 ^ 40 * 8109539 * 2
def baseEnd_8109539 : Nat := 1388030464460550708355805

theorem tailTrace_8109539 : CollatzResearch.WordTrace tailWord_8109539 prefixEnd_8109539 1388030464460550708355805 := by
  unfold tailWord_8109539
  simp only [CollatzResearch.WordTrace]
  refine ⟨295779186567532676840907671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197186124378355117893938447 295779186567532676840907671)
  ·
    refine ⟨443668779851299015261361507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295779186567532676840907671 443668779851299015261361507)
    ·
      refine ⟨665503169776948522892042261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443668779851299015261361507 665503169776948522892042261)
      ·
        refine ⟨31195461083294462010564481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 665503169776948522892042261 31195461083294462010564481)
        ·
          refine ⟨23396595812470846507923361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31195461083294462010564481 23396595812470846507923361)
          ·
            refine ⟨17547446859353134880942521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23396595812470846507923361 17547446859353134880942521)
            ·
              refine ⟨13160585144514851160706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17547446859353134880942521 13160585144514851160706891)
              ·
                refine ⟨19740877716772276741060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13160585144514851160706891 19740877716772276741060337)
                ·
                  refine ⟨14805658287579207555795253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19740877716772276741060337 14805658287579207555795253)
                  ·
                    refine ⟨1388030464460550708355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14805658287579207555795253 1388030464460550708355805)
                    ·
                      rfl

theorem cell23_8109539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 5].length) (baseStart_8109539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109539 prefixEnd_8109539 := by exact prefixLift 8109539
  have htrace : WordTrace (prefixWord ++ tailWord_8109539) baseStart_8109539 baseEnd_8109539 := by
    simpa [prefixWord, tailWord_8109539, baseEnd_8109539] using wordTrace_append hprefix tailTrace_8109539
  have hstable : (prefixWord ++ tailWord_8109539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109539).length < 2 ^ (prefixWord ++ tailWord_8109539).sum := by decide
  have hdescent : baseEnd_8109539 < baseStart_8109539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109603 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 1, 4]
def baseStart_8109603 : Nat := 118140960795 + 8109603 * 2 ^ 59
def prefixEnd_8109603 : Nat := 4983230072969 + 3 ^ 40 * 8109603 * 2
def baseEnd_8109603 : Nat := 1388041418714513291555707

theorem tailTrace_8109603 : CollatzResearch.WordTrace tailWord_8109603 prefixEnd_8109603 1388041418714513291555707 := by
  unfold tailWord_8109603
  simp only [CollatzResearch.WordTrace]
  refine ⟨295781520839300815771237463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197187680559533877180824975 295781520839300815771237463)
  ·
    refine ⟨443672281258951223656856195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295781520839300815771237463 443672281258951223656856195)
    ·
      refine ⟨665508421888426835485284293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443672281258951223656856195 665508421888426835485284293)
      ·
        refine ⟨124782829104080031653490805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665508421888426835485284293 124782829104080031653490805)
        ·
          refine ⟨11698390228507502967514763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124782829104080031653490805 11698390228507502967514763)
          ·
            refine ⟨17547585342761254451272145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698390228507502967514763 17547585342761254451272145)
            ·
              refine ⟨13160689007070940838454109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17547585342761254451272145 13160689007070940838454109)
              ·
                refine ⟨4935258377651602814420291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160689007070940838454109 4935258377651602814420291)
                ·
                  refine ⟨7402887566477404221630437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935258377651602814420291 7402887566477404221630437)
                  ·
                    refine ⟨1388041418714513291555707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402887566477404221630437 1388041418714513291555707)
                    ·
                      rfl

theorem cell23_8109603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 4].length) (baseStart_8109603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109603 prefixEnd_8109603 := by exact prefixLift 8109603
  have htrace : WordTrace (prefixWord ++ tailWord_8109603) baseStart_8109603 baseEnd_8109603 := by
    simpa [prefixWord, tailWord_8109603, baseEnd_8109603] using wordTrace_append hprefix tailTrace_8109603
  have hstable : (prefixWord ++ tailWord_8109603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109603).length < 2 ^ (prefixWord ++ tailWord_8109603).sum := by decide
  have hdescent : baseEnd_8109603 < baseStart_8109603 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109626 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_8109626 : Nat := 118140960795 + 8109626 * 2 ^ 59
def prefixEnd_8109626 : Nat := 4983230072969 + 3 ^ 40 * 8109626 * 2
def baseEnd_8109626 : Nat := 4164136066198593284679515

theorem tailTrace_8109626 : CollatzResearch.WordTrace tailWord_8109626 prefixEnd_8109626 4164136066198593284679515 := by
  unfold tailWord_8109626
  simp only [CollatzResearch.WordTrace]
  refine ⟨73945589929554372674831183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197188239812144993799549821 73945589929554372674831183)
  ·
    refine ⟨110918384894331559012246775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73945589929554372674831183 110918384894331559012246775)
    ·
      refine ⟨166377577341497338518370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110918384894331559012246775 166377577341497338518370163)
      ·
        refine ⟨249566366012246007777555245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166377577341497338518370163 249566366012246007777555245)
        ·
          refine ⟨93587387254592252916583217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249566366012246007777555245 93587387254592252916583217)
          ·
            refine ⟨70190540440944189687437413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93587387254592252916583217 70190540440944189687437413)
            ·
              refine ⟨13160726332677035566394515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70190540440944189687437413 13160726332677035566394515)
              ·
                refine ⟨19741089499015553349591773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13160726332677035566394515 19741089499015553349591773)
                ·
                  refine ⟨7402908562130832506096915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19741089499015553349591773 7402908562130832506096915)
                  ·
                    refine ⟨11104362843196248759145373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402908562130832506096915 11104362843196248759145373)
                    ·
                      refine ⟨4164136066198593284679515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104362843196248759145373 4164136066198593284679515)
                      ·
                        rfl

theorem cell23_8109626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_8109626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109626 prefixEnd_8109626 := by exact prefixLift 8109626
  have htrace : WordTrace (prefixWord ++ tailWord_8109626) baseStart_8109626 baseEnd_8109626 := by
    simpa [prefixWord, tailWord_8109626, baseEnd_8109626] using wordTrace_append hprefix tailTrace_8109626
  have hstable : (prefixWord ++ tailWord_8109626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109626).length < 2 ^ (prefixWord ++ tailWord_8109626).sum := by decide
  have hdescent : baseEnd_8109626 < baseStart_8109626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109649 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_8109649 : Nat := 118140960795 + 8109649 * 2 ^ 59
def prefixEnd_8109649 : Nat := 4983230072969 + 3 ^ 40 * 8109649 * 2
def baseEnd_8109649 : Nat := 4164147876253646694691909

theorem tailTrace_8109649 : CollatzResearch.WordTrace tailWord_8109649 prefixEnd_8109649 4164147876253646694691909 := by
  unfold tailWord_8109649
  simp only [CollatzResearch.WordTrace]
  refine ⟨295783198597134165627412001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197188799064756110418274667 295783198597134165627412001)
  ·
    refine ⟨221837398947850624220559001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295783198597134165627412001 221837398947850624220559001)
    ·
      refine ⟨166378049210887968165419251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221837398947850624220559001 166378049210887968165419251)
      ·
        refine ⟨249567073816331952248128877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166378049210887968165419251 249567073816331952248128877)
        ·
          refine ⟨93587652681124482093048329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249567073816331952248128877 93587652681124482093048329)
          ·
            refine ⟨70190739510843361569786247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93587652681124482093048329 70190739510843361569786247)
            ·
              refine ⟨105286109266265042354679371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70190739510843361569786247 105286109266265042354679371)
              ·
                refine ⟨157929163899397563532019057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105286109266265042354679371 157929163899397563532019057)
                ·
                  refine ⟨118446872924548172649014293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157929163899397563532019057 118446872924548172649014293)
                  ·
                    refine ⟨5552197168338195592922545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118446872924548172649014293 5552197168338195592922545)
                    ·
                      refine ⟨4164147876253646694691909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552197168338195592922545 4164147876253646694691909)
                      ·
                        rfl

theorem cell23_8109649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_8109649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109649 prefixEnd_8109649 := by exact prefixLift 8109649
  have htrace : WordTrace (prefixWord ++ tailWord_8109649) baseStart_8109649 baseEnd_8109649 := by
    simpa [prefixWord, tailWord_8109649, baseEnd_8109649] using wordTrace_append hprefix tailTrace_8109649
  have hstable : (prefixWord ++ tailWord_8109649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109649).length < 2 ^ (prefixWord ++ tailWord_8109649).sum := by decide
  have hdescent : baseEnd_8109649 < baseStart_8109649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109654 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_8109654 : Nat := 118140960795 + 8109654 * 2 ^ 59
def prefixEnd_8109654 : Nat := 4983230072969 + 3 ^ 40 * 8109654 * 2
def baseEnd_8109654 : Nat := 1388050147885639725043129

theorem tailTrace_8109654 : CollatzResearch.WordTrace tailWord_8109654 prefixEnd_8109654 1388050147885639725043129 := by
  unfold tailWord_8109654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486461310132253217584001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197188920641410700987562677 18486461310132253217584001)
  ·
    refine ⟨13864845982599189913188001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18486461310132253217584001 13864845982599189913188001)
    ·
      refine ⟨10398634486949392434891001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13864845982599189913188001 10398634486949392434891001)
      ·
        refine ⟨7798975865212044326168251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10398634486949392434891001 7798975865212044326168251)
        ·
          refine ⟨11698463797818066489252377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798975865212044326168251 11698463797818066489252377)
          ·
            refine ⟨8773847848363549866939283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11698463797818066489252377 8773847848363549866939283)
            ·
              refine ⟨13160771772545324800408925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773847848363549866939283 13160771772545324800408925)
              ·
                refine ⟨4935289414704496800153347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160771772545324800408925 4935289414704496800153347)
                ·
                  refine ⟨7402934122056745200230021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935289414704496800153347 7402934122056745200230021)
                  ·
                    refine ⟨1388050147885639725043129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402934122056745200230021 1388050147885639725043129)
                    ·
                      rfl

theorem cell23_8109654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_8109654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109654 prefixEnd_8109654 := by exact prefixLift 8109654
  have htrace : WordTrace (prefixWord ++ tailWord_8109654) baseStart_8109654 baseEnd_8109654 := by
    simpa [prefixWord, tailWord_8109654, baseEnd_8109654] using wordTrace_append hprefix tailTrace_8109654
  have hstable : (prefixWord ++ tailWord_8109654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109654).length < 2 ^ (prefixWord ++ tailWord_8109654).sum := by decide
  have hdescent : baseEnd_8109654 < baseStart_8109654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109660 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_8109660 : Nat := 118140960795 + 8109660 * 2 ^ 59
def prefixEnd_8109660 : Nat := 4983230072969 + 3 ^ 40 * 8109660 * 2
def baseEnd_8109660 : Nat := 4164153524540846151654359

theorem tailTrace_8109660 : CollatzResearch.WordTrace tailWord_8109660 prefixEnd_8109660 4164153524540846151654359 := by
  unfold tailWord_8109660
  simp only [CollatzResearch.WordTrace]
  refine ⟨147891799900047157253031217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197189066533396209670708289 147891799900047157253031217)
  ·
    refine ⟨110918849925035367939773413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147891799900047157253031217 110918849925035367939773413)
    ·
      refine ⟨20797284360944131488707515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110918849925035367939773413 20797284360944131488707515)
      ·
        refine ⟨31195926541416197233061273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797284360944131488707515 31195926541416197233061273)
        ·
          refine ⟨23396944906062147924795955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31195926541416197233061273 23396944906062147924795955)
          ·
            refine ⟨35095417359093221887193933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23396944906062147924795955 35095417359093221887193933)
            ·
              refine ⟨13160781509659958207697725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35095417359093221887193933 13160781509659958207697725)
              ·
                refine ⟨4935293066122484327886647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13160781509659958207697725 4935293066122484327886647)
                ·
                  refine ⟨7402939599183726491829971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935293066122484327886647 7402939599183726491829971)
                  ·
                    refine ⟨11104409398775589737744957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402939599183726491829971 11104409398775589737744957)
                    ·
                      refine ⟨4164153524540846151654359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104409398775589737744957 4164153524540846151654359)
                      ·
                        rfl

theorem cell23_8109660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_8109660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109660 prefixEnd_8109660 := by exact prefixLift 8109660
  have htrace : WordTrace (prefixWord ++ tailWord_8109660) baseStart_8109660 baseEnd_8109660 := by
    simpa [prefixWord, tailWord_8109660, baseEnd_8109660] using wordTrace_append hprefix tailTrace_8109660
  have hstable : (prefixWord ++ tailWord_8109660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109660).length < 2 ^ (prefixWord ++ tailWord_8109660).sum := by decide
  have hdescent : baseEnd_8109660 < baseStart_8109660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109669 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_8109669 : Nat := 118140960795 + 8109669 * 2 ^ 59
def prefixEnd_8109669 : Nat := 4983230072969 + 3 ^ 40 * 8109669 * 2
def baseEnd_8109669 : Nat := 4164158145866736616441817

theorem tailTrace_8109669 : CollatzResearch.WordTrace tailWord_8109669 prefixEnd_8109669 4164158145866736616441817 := by
  unfold tailWord_8109669
  simp only [CollatzResearch.WordTrace]
  refine ⟨295783928057061709043140061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197189285371374472695426707 295783928057061709043140061)
  ·
    refine ⟨110918973021398140891177523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295783928057061709043140061 110918973021398140891177523)
    ·
      refine ⟨166378459532097211336766285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110918973021398140891177523 166378459532097211336766285)
      ·
        refine ⟨62391922324536454251287357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166378459532097211336766285 62391922324536454251287357)
        ·
          refine ⟨23396970871701170344232759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62391922324536454251287357 23396970871701170344232759)
          ·
            refine ⟨35095456307551755516349139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23396970871701170344232759 35095456307551755516349139)
            ·
              refine ⟨52643184461327633274523709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35095456307551755516349139 52643184461327633274523709)
              ·
                refine ⟨19741194172997862477946391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52643184461327633274523709 19741194172997862477946391)
                ·
                  refine ⟨29611791259496793716919587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741194172997862477946391 29611791259496793716919587)
                  ·
                    refine ⟨44417686889245190575379381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29611791259496793716919587 44417686889245190575379381)
                    ·
                      refine ⟨4164158145866736616441817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44417686889245190575379381 4164158145866736616441817)
                      ·
                        rfl

theorem cell23_8109669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_8109669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109669 prefixEnd_8109669 := by exact prefixLift 8109669
  have htrace : WordTrace (prefixWord ++ tailWord_8109669) baseStart_8109669 baseEnd_8109669 := by
    simpa [prefixWord, tailWord_8109669, baseEnd_8109669] using wordTrace_append hprefix tailTrace_8109669
  have hstable : (prefixWord ++ tailWord_8109669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109669).length < 2 ^ (prefixWord ++ tailWord_8109669).sum := by decide
  have hdescent : baseEnd_8109669 < baseStart_8109669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109677 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_8109677 : Nat := 118140960795 + 8109677 * 2 ^ 59
def prefixEnd_8109677 : Nat := 4983230072969 + 3 ^ 40 * 8109677 * 2
def baseEnd_8109677 : Nat := 4164162253711972585141781

theorem tailTrace_8109677 : CollatzResearch.WordTrace tailWord_8109677 prefixEnd_8109677 4164162253711972585141781 := by
  unfold tailWord_8109677
  simp only [CollatzResearch.WordTrace]
  refine ⟨295784219841032726409431285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197189479894021817606287523 295784219841032726409431285)
  ·
    refine ⟨27729770610096818100884183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295784219841032726409431285 27729770610096818100884183)
    ·
      refine ⟨41594655915145227151326275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27729770610096818100884183 41594655915145227151326275)
      ·
        refine ⟨62391983872717840726989413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41594655915145227151326275 62391983872717840726989413)
        ·
          refine ⟨11698496976134595136310515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62391983872717840726989413 11698496976134595136310515)
          ·
            refine ⟨17547745464201892704465773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698496976134595136310515 17547745464201892704465773)
            ·
              refine ⟨6580404549075709764174665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17547745464201892704465773 6580404549075709764174665)
              ·
                refine ⟨4935303411806782323130999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580404549075709764174665 4935303411806782323130999)
                ·
                  refine ⟨7402955117710173484696499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935303411806782323130999 7402955117710173484696499)
                  ·
                    refine ⟨11104432676565260227044749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7402955117710173484696499 11104432676565260227044749)
                    ·
                      refine ⟨4164162253711972585141781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104432676565260227044749 4164162253711972585141781)
                      ·
                        rfl

theorem cell23_8109677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_8109677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109677 prefixEnd_8109677 := by exact prefixLift 8109677
  have htrace : WordTrace (prefixWord ++ tailWord_8109677) baseStart_8109677 baseEnd_8109677 := by
    simpa [prefixWord, tailWord_8109677, baseEnd_8109677] using wordTrace_append hprefix tailTrace_8109677
  have hstable : (prefixWord ++ tailWord_8109677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109677).length < 2 ^ (prefixWord ++ tailWord_8109677).sum := by decide
  have hdescent : baseEnd_8109677 < baseStart_8109677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109686 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8109686 : Nat := 118140960795 + 8109686 * 2 ^ 59
def prefixEnd_8109686 : Nat := 4983230072969 + 3 ^ 40 * 8109686 * 2
def baseEnd_8109686 : Nat := 4164166875037863049929239

theorem tailTrace_8109686 : CollatzResearch.WordTrace tailWord_8109686 prefixEnd_8109686 4164166875037863049929239 := by
  unfold tailWord_8109686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486534256125007559156807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197189698732000080631005941 18486534256125007559156807)
  ·
    refine ⟨27729801384187511338735211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18486534256125007559156807 27729801384187511338735211)
    ·
      refine ⟨41594702076281267008102817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27729801384187511338735211 41594702076281267008102817)
      ·
        refine ⟨31196026557210950256077113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41594702076281267008102817 31196026557210950256077113)
        ·
          refine ⟨23397019917908212692057835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31196026557210950256077113 23397019917908212692057835)
          ·
            refine ⟨35095529876862319038086753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23397019917908212692057835 35095529876862319038086753)
            ·
              refine ⟨26321647407646739278565065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35095529876862319038086753 26321647407646739278565065)
              ·
                refine ⟨19741235555735054458923799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26321647407646739278565065 19741235555735054458923799)
                ·
                  refine ⟨29611853333602581688385699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741235555735054458923799 29611853333602581688385699)
                  ·
                    refine ⟨44417780000403872532578549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29611853333602581688385699 44417780000403872532578549)
                    ·
                      refine ⟨4164166875037863049929239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44417780000403872532578549 4164166875037863049929239)
                      ·
                        rfl

theorem cell23_8109686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8109686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109686 prefixEnd_8109686 := by exact prefixLift 8109686
  have htrace : WordTrace (prefixWord ++ tailWord_8109686) baseStart_8109686 baseEnd_8109686 := by
    simpa [prefixWord, tailWord_8109686, baseEnd_8109686] using wordTrace_append hprefix tailTrace_8109686
  have hstable : (prefixWord ++ tailWord_8109686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109686).length < 2 ^ (prefixWord ++ tailWord_8109686).sum := by decide
  have hdescent : baseEnd_8109686 < baseStart_8109686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_8109692 : Nat := 118140960795 + 8109692 * 2 ^ 59
def prefixEnd_8109692 : Nat := 4983230072969 + 3 ^ 40 * 8109692 * 2
def baseEnd_8109692 : Nat := 4164169955921790026454211

theorem tailTrace_8109692 : CollatzResearch.WordTrace tailWord_8109692 prefixEnd_8109692 4164169955921790026454211 := by
  unfold tailWord_8109692
  simp only [CollatzResearch.WordTrace]
  refine ⟨147892383467989191985613665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197189844623985589314151553 147892383467989191985613665)
  ·
    refine ⟨110919287600991893989210249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147892383467989191985613665 110919287600991893989210249)
    ·
      refine ⟨83189465700743920491907687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110919287600991893989210249 83189465700743920491907687)
      ·
        refine ⟨124784198551115880737861531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83189465700743920491907687 124784198551115880737861531)
        ·
          refine ⟨187176297826673821106792297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124784198551115880737861531 187176297826673821106792297)
          ·
            refine ⟨140382223370005365830094223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187176297826673821106792297 140382223370005365830094223)
            ·
              refine ⟨210573335055008048745141335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140382223370005365830094223 210573335055008048745141335)
              ·
                refine ⟨315860002582512073117712003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210573335055008048745141335 315860002582512073117712003)
                ·
                  refine ⟨473790003873768109676568005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315860002582512073117712003 473790003873768109676568005)
                  ·
                    refine ⟨88835625726331520564356501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473790003873768109676568005 88835625726331520564356501)
                    ·
                      refine ⟨4164169955921790026454211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88835625726331520564356501 4164169955921790026454211)
                      ·
                        rfl

theorem cell23_8109692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_8109692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109692 prefixEnd_8109692 := by exact prefixLift 8109692
  have htrace : WordTrace (prefixWord ++ tailWord_8109692) baseStart_8109692 baseEnd_8109692 := by
    simpa [prefixWord, tailWord_8109692, baseEnd_8109692] using wordTrace_append hprefix tailTrace_8109692
  have hstable : (prefixWord ++ tailWord_8109692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109692).length < 2 ^ (prefixWord ++ tailWord_8109692).sum := by decide
  have hdescent : baseEnd_8109692 < baseStart_8109692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109693 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_8109693 : Nat := 118140960795 + 8109693 * 2 ^ 59
def prefixEnd_8109693 : Nat := 4983230072969 + 3 ^ 40 * 8109693 * 2
def baseEnd_8109693 : Nat := 1388056823134148174180569

theorem tailTrace_8109693 : CollatzResearch.WordTrace tailWord_8109693 prefixEnd_8109693 1388056823134148174180569 := by
  unfold tailWord_8109693
  simp only [CollatzResearch.WordTrace]
  refine ⟨295784803408974761142013733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197189868939316507428009155 295784803408974761142013733)
  ·
    refine ⟨55459650639182767714127575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295784803408974761142013733 55459650639182767714127575)
    ·
      refine ⟨83189475958774151571191363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55459650639182767714127575 83189475958774151571191363)
      ·
        refine ⟨124784213938161227356787045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83189475958774151571191363 124784213938161227356787045)
        ·
          refine ⟨23397040113405230129397571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124784213938161227356787045 23397040113405230129397571)
          ·
            refine ⟨35095560170107845194096357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23397040113405230129397571 35095560170107845194096357)
            ·
              refine ⟨6580417531895220973893067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35095560170107845194096357 6580417531895220973893067)
              ·
                refine ⟨9870626297842831460839601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580417531895220973893067 9870626297842831460839601)
                ·
                  refine ⟨7402969723382123595629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9870626297842831460839601 7402969723382123595629701)
                  ·
                    refine ⟨1388056823134148174180569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402969723382123595629701 1388056823134148174180569)
                    ·
                      rfl

theorem cell23_8109693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_8109693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109693 prefixEnd_8109693 := by exact prefixLift 8109693
  have htrace : WordTrace (prefixWord ++ tailWord_8109693) baseStart_8109693 baseEnd_8109693 := by
    simpa [prefixWord, tailWord_8109693, baseEnd_8109693] using wordTrace_append hprefix tailTrace_8109693
  have hstable : (prefixWord ++ tailWord_8109693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109693).length < 2 ^ (prefixWord ++ tailWord_8109693).sum := by decide
  have hdescent : baseEnd_8109693 < baseStart_8109693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109699 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3]
def baseStart_8109699 : Nat := 118140960795 + 8109699 * 2 ^ 59
def prefixEnd_8109699 : Nat := 4983230072969 + 3 ^ 40 * 8109699 * 2
def baseEnd_8109699 : Nat := 4164173550286371499066679

theorem tailTrace_8109699 : CollatzResearch.WordTrace tailWord_8109699 prefixEnd_8109699 4164173550286371499066679 := by
  unfold tailWord_8109699
  simp only [CollatzResearch.WordTrace]
  refine ⟨295785022246953024166732151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197190014831302016111154767 295785022246953024166732151)
  ·
    refine ⟨443677533370429536250098227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295785022246953024166732151 443677533370429536250098227)
    ·
      refine ⟨665516300055644304375147341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443677533370429536250098227 665516300055644304375147341)
      ·
        refine ⟨249568612520866614140680253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665516300055644304375147341 249568612520866614140680253)
        ·
          refine ⟨93588229695324980302755095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249568612520866614140680253 93588229695324980302755095)
          ·
            refine ⟨140382344542987470454132643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93588229695324980302755095 140382344542987470454132643)
            ·
              refine ⟨210573516814481205681198965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140382344542987470454132643 210573516814481205681198965)
              ·
                refine ⟨19741267201357613032612403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210573516814481205681198965 19741267201357613032612403)
                ·
                  refine ⟨29611900802036419548918605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741267201357613032612403 29611900802036419548918605)
                  ·
                    refine ⟨11104462800763657330844477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29611900802036419548918605 11104462800763657330844477)
                    ·
                      refine ⟨4164173550286371499066679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104462800763657330844477 4164173550286371499066679)
                      ·
                        rfl

theorem cell23_8109699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_8109699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109699 prefixEnd_8109699 := by exact prefixLift 8109699
  have htrace : WordTrace (prefixWord ++ tailWord_8109699) baseStart_8109699 baseEnd_8109699 := by
    simpa [prefixWord, tailWord_8109699, baseEnd_8109699] using wordTrace_append hprefix tailTrace_8109699
  have hstable : (prefixWord ++ tailWord_8109699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109699).length < 2 ^ (prefixWord ++ tailWord_8109699).sum := by decide
  have hdescent : baseEnd_8109699 < baseStart_8109699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109700 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_8109700 : Nat := 118140960795 + 8109700 * 2 ^ 59
def prefixEnd_8109700 : Nat := 4983230072969 + 3 ^ 40 * 8109700 * 2
def baseEnd_8109700 : Nat := 4164174063767025995154175

theorem tailTrace_8109700 : CollatzResearch.WordTrace tailWord_8109700 prefixEnd_8109700 4164174063767025995154175 := by
  unfold tailWord_8109700
  simp only [CollatzResearch.WordTrace]
  refine ⟨147892529359974700668759277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197190039146632934225012369 147892529359974700668759277)
  ·
    refine ⟨55459698509990512750784729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147892529359974700668759277 55459698509990512750784729)
    ·
      refine ⟨41594773882492884563088547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55459698509990512750784729 41594773882492884563088547)
      ·
        refine ⟨62392160823739326844632821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41594773882492884563088547 62392160823739326844632821)
        ·
          refine ⟨5849265077225561891684327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62392160823739326844632821 5849265077225561891684327)
          ·
            refine ⟨8773897615838342837526491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849265077225561891684327 8773897615838342837526491)
            ·
              refine ⟨13160846423757514256289737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773897615838342837526491 13160846423757514256289737)
              ·
                refine ⟨9870634817818135692217303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13160846423757514256289737 9870634817818135692217303)
                ·
                  refine ⟨14805952226727203538325955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9870634817818135692217303 14805952226727203538325955)
                  ·
                    refine ⟨22208928340090805307488933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14805952226727203538325955 22208928340090805307488933)
                    ·
                      refine ⟨4164174063767025995154175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22208928340090805307488933 4164174063767025995154175)
                      ·
                        rfl

theorem cell23_8109700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_8109700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109700 prefixEnd_8109700 := by exact prefixLift 8109700
  have htrace : WordTrace (prefixWord ++ tailWord_8109700) baseStart_8109700 baseEnd_8109700 := by
    simpa [prefixWord, tailWord_8109700, baseEnd_8109700] using wordTrace_append hprefix tailTrace_8109700
  have hstable : (prefixWord ++ tailWord_8109700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109700).length < 2 ^ (prefixWord ++ tailWord_8109700).sum := by decide
  have hdescent : baseEnd_8109700 < baseStart_8109700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109703 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_8109703 : Nat := 118140960795 + 8109703 * 2 ^ 59
def prefixEnd_8109703 : Nat := 4983230072969 + 3 ^ 40 * 8109703 * 2
def baseEnd_8109703 : Nat := 4164175604208989483416661

theorem tailTrace_8109703 : CollatzResearch.WordTrace tailWord_8109703 prefixEnd_8109703 4164175604208989483416661 := by
  unfold tailWord_8109703
  simp only [CollatzResearch.WordTrace]
  refine ⟨295785168138938532849877763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197190112092625688566585175 295785168138938532849877763)
  ·
    refine ⟨443677752208407799274816645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295785168138938532849877763 443677752208407799274816645)
    ·
      refine ⟨83189578539076462364028121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443677752208407799274816645 83189578539076462364028121)
      ·
        refine ⟨62392183904307346773021091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83189578539076462364028121 62392183904307346773021091)
        ·
          refine ⟨93588275856461020159531637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62392183904307346773021091 93588275856461020159531637)
          ·
            refine ⟨8773900861543220639956091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93588275856461020159531637 8773900861543220639956091)
            ·
              refine ⟨13160851292314830959934137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8773900861543220639956091 13160851292314830959934137)
              ·
                refine ⟨9870638469236123219950603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13160851292314830959934137 9870638469236123219950603)
                ·
                  refine ⟨14805957703854184829925905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9870638469236123219950603 14805957703854184829925905)
                  ·
                    refine ⟨11104468277890638622444429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14805957703854184829925905 11104468277890638622444429)
                    ·
                      refine ⟨4164175604208989483416661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104468277890638622444429 4164175604208989483416661)
                      ·
                        rfl

theorem cell23_8109703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_8109703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109703 prefixEnd_8109703 := by exact prefixLift 8109703
  have htrace : WordTrace (prefixWord ++ tailWord_8109703) baseStart_8109703 baseEnd_8109703 := by
    simpa [prefixWord, tailWord_8109703, baseEnd_8109703] using wordTrace_append hprefix tailTrace_8109703
  have hstable : (prefixWord ++ tailWord_8109703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109703).length < 2 ^ (prefixWord ++ tailWord_8109703).sum := by decide
  have hdescent : baseEnd_8109703 < baseStart_8109703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109712 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_8109712 : Nat := 118140960795 + 8109712 * 2 ^ 59
def prefixEnd_8109712 : Nat := 4983230072969 + 3 ^ 40 * 8109712 * 2
def baseEnd_8109712 : Nat := 4164180225534879948204119

theorem tailTrace_8109712 : CollatzResearch.WordTrace tailWord_8109712 prefixEnd_8109712 4164180225534879948204119 := by
  unfold tailWord_8109712
  simp only [CollatzResearch.WordTrace]
  refine ⟨147892748197952963693477695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197190330930603951591303593 147892748197952963693477695)
  ·
    refine ⟨221839122296929445540216543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147892748197952963693477695 221839122296929445540216543)
    ·
      refine ⟨332758683445394168310324815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221839122296929445540216543 332758683445394168310324815)
      ·
        refine ⟨499138025168091252465487223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332758683445394168310324815 499138025168091252465487223)
        ·
          refine ⟨748707037752136878698230835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499138025168091252465487223 748707037752136878698230835)
          ·
            refine ⟨1123060556628205318047346253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748707037752136878698230835 1123060556628205318047346253)
            ·
              refine ⟨421147708735576994267754845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123060556628205318047346253 421147708735576994267754845)
              ·
                refine ⟨157930390775841372850408067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421147708735576994267754845 157930390775841372850408067)
                ·
                  refine ⟨236895586163762059275612101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157930390775841372850408067 236895586163762059275612101)
                  ·
                    refine ⟨44417922405705386114177269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236895586163762059275612101 44417922405705386114177269)
                    ·
                      refine ⟨4164180225534879948204119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44417922405705386114177269 4164180225534879948204119)
                      ·
                        rfl

theorem cell23_8109712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_8109712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109712 prefixEnd_8109712 := by exact prefixLift 8109712
  have htrace : WordTrace (prefixWord ++ tailWord_8109712) baseStart_8109712 baseEnd_8109712 := by
    simpa [prefixWord, tailWord_8109712, baseEnd_8109712] using wordTrace_append hprefix tailTrace_8109712
  have hstable : (prefixWord ++ tailWord_8109712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109712).length < 2 ^ (prefixWord ++ tailWord_8109712).sum := by decide
  have hdescent : baseEnd_8109712 < baseStart_8109712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109750 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_8109750 : Nat := 118140960795 + 8109750 * 2 ^ 59
def prefixEnd_8109750 : Nat := 4983230072969 + 3 ^ 40 * 8109750 * 2
def baseEnd_8109750 : Nat := 4164199737799750799528945

theorem tailTrace_8109750 : CollatzResearch.WordTrace tailWord_8109750 prefixEnd_8109750 4164199737799750799528945 := by
  unfold tailWord_8109750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486680148110516242302419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197191254913178839917892469 18486680148110516242302419)
  ·
    refine ⟨27730020222165774363453629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18486680148110516242302419 27730020222165774363453629)
    ·
      refine ⟨10398757583312165386295111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27730020222165774363453629 10398757583312165386295111)
      ·
        refine ⟨15598136374968248079442667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398757583312165386295111 15598136374968248079442667)
        ·
          refine ⟨23397204562452372119164001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598136374968248079442667 23397204562452372119164001)
          ·
            refine ⟨17547903421839279089373001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397204562452372119164001 17547903421839279089373001)
            ·
              refine ⟨13160927566379459317029751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17547903421839279089373001 13160927566379459317029751)
              ·
                refine ⟨19741391349569188975544627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13160927566379459317029751 19741391349569188975544627)
                ·
                  refine ⟨29612087024353783463316941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741391349569188975544627 29612087024353783463316941)
                  ·
                    refine ⟨11104532634132668798743853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29612087024353783463316941 11104532634132668798743853)
                    ·
                      refine ⟨4164199737799750799528945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104532634132668798743853 4164199737799750799528945)
                      ·
                        rfl

theorem cell23_8109750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_8109750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109750 prefixEnd_8109750 := by exact prefixLift 8109750
  have htrace : WordTrace (prefixWord ++ tailWord_8109750) baseStart_8109750 baseEnd_8109750 := by
    simpa [prefixWord, tailWord_8109750, baseEnd_8109750] using wordTrace_append hprefix tailTrace_8109750
  have hstable : (prefixWord ++ tailWord_8109750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109750).length < 2 ^ (prefixWord ++ tailWord_8109750).sum := by decide
  have hdescent : baseEnd_8109750 < baseStart_8109750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109759 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3]
def baseStart_8109759 : Nat := 118140960795 + 8109759 * 2 ^ 59
def prefixEnd_8109759 : Nat := 4983230072969 + 3 ^ 40 * 8109759 * 2
def baseEnd_8109759 : Nat := 4164204359125641264316403

theorem tailTrace_8109759 : CollatzResearch.WordTrace tailWord_8109759 prefixEnd_8109759 4164204359125641264316403 := by
  unfold tailWord_8109759
  simp only [CollatzResearch.WordTrace]
  refine ⟨295787210626735654413916331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197191473751157102942610887 295787210626735654413916331)
  ·
    refine ⟨443680815940103481620874497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295787210626735654413916331 443680815940103481620874497)
    ·
      refine ⟨332760611955077611215655873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443680815940103481620874497 332760611955077611215655873)
      ·
        refine ⟨249570458966308208411741905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332760611955077611215655873 249570458966308208411741905)
        ·
          refine ⟨187177844224731156308806429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249570458966308208411741905 187177844224731156308806429)
          ·
            refine ⟨70191691584274183615802411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187177844224731156308806429 70191691584274183615802411)
            ·
              refine ⟨105287537376411275423703617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70191691584274183615802411 105287537376411275423703617)
              ·
                refine ⟨78965653032308456567777713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105287537376411275423703617 78965653032308456567777713)
                ·
                  refine ⟨59224239774231342425833285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78965653032308456567777713 59224239774231342425833285)
                  ·
                    refine ⟨11104544957668376704843741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59224239774231342425833285 11104544957668376704843741)
                    ·
                      refine ⟨4164204359125641264316403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104544957668376704843741 4164204359125641264316403)
                      ·
                        rfl

theorem cell23_8109759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_8109759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109759 prefixEnd_8109759 := by exact prefixLift 8109759
  have htrace : WordTrace (prefixWord ++ tailWord_8109759) baseStart_8109759 baseEnd_8109759 := by
    simpa [prefixWord, tailWord_8109759, baseEnd_8109759] using wordTrace_append hprefix tailTrace_8109759
  have hstable : (prefixWord ++ tailWord_8109759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109759).length < 2 ^ (prefixWord ++ tailWord_8109759).sum := by decide
  have hdescent : baseEnd_8109759 < baseStart_8109759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109796 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 5]
def baseStart_8109796 : Nat := 118140960795 + 8109796 * 2 ^ 59
def prefixEnd_8109796 : Nat := 4983230072969 + 3 ^ 40 * 8109796 * 2
def baseEnd_8109796 : Nat := 462691484212206402172637

theorem tailTrace_8109796 : CollatzResearch.WordTrace tailWord_8109796 prefixEnd_8109796 462691484212206402172637 := by
  unfold tailWord_8109796
  simp only [CollatzResearch.WordTrace]
  refine ⟨147894280063800804866506621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197192373418401073155342161 147894280063800804866506621)
  ·
    refine ⟨55460355023925301824939983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147894280063800804866506621 55460355023925301824939983)
    ·
      refine ⟨83190532535887952737409975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55460355023925301824939983 83190532535887952737409975)
      ·
        refine ⟨124785798803831929106114963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83190532535887952737409975 124785798803831929106114963)
        ·
          refine ⟨187178698205747893659172445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124785798803831929106114963 187178698205747893659172445)
          ·
            refine ⟨70192011827155460122189667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187178698205747893659172445 70192011827155460122189667)
            ·
              refine ⟨105288017740733190183284501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70192011827155460122189667 105288017740733190183284501)
              ·
                refine ⟨4935375831596868289841461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105288017740733190183284501 4935375831596868289841461)
                ·
                  refine ⟨462691484212206402172637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935375831596868289841461 462691484212206402172637)
                  ·
                    rfl

theorem cell23_8109796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_8109796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109796 prefixEnd_8109796 := by exact prefixLift 8109796
  have htrace : WordTrace (prefixWord ++ tailWord_8109796) baseStart_8109796 baseEnd_8109796 := by
    simpa [prefixWord, tailWord_8109796, baseEnd_8109796] using wordTrace_append hprefix tailTrace_8109796
  have hstable : (prefixWord ++ tailWord_8109796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109796).length < 2 ^ (prefixWord ++ tailWord_8109796).sum := by decide
  have hdescent : baseEnd_8109796 < baseStart_8109796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109806 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_8109806 : Nat := 118140960795 + 8109806 * 2 ^ 59
def prefixEnd_8109806 : Nat := 4983230072969 + 3 ^ 40 * 8109806 * 2
def baseEnd_8109806 : Nat := 4164228492716402580428687

theorem tailTrace_8109806 : CollatzResearch.WordTrace tailWord_8109806 prefixEnd_8109806 4164228492716402580428687 := by
  unfold tailWord_8109806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36973615607195672680109659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197192616571710254293918181 36973615607195672680109659)
  ·
    refine ⟨55460423410793509020164489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36973615607195672680109659 55460423410793509020164489)
    ·
      refine ⟨41595317558095131765123367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55460423410793509020164489 41595317558095131765123367)
      ·
        refine ⟨62392976337142697647685051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41595317558095131765123367 62392976337142697647685051)
        ·
          refine ⟨93589464505714046471527577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62392976337142697647685051 93589464505714046471527577)
          ·
            refine ⟨70192098379285534853645683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93589464505714046471527577 70192098379285534853645683)
            ·
              refine ⟨105288147568928302280468525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70192098379285534853645683 105288147568928302280468525)
              ·
                refine ⟨39483055338348113355175697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105288147568928302280468525 39483055338348113355175697)
                ·
                  refine ⟨29612291503761085016381773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39483055338348113355175697 29612291503761085016381773)
                  ·
                    refine ⟨11104609313910406881143165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29612291503761085016381773 11104609313910406881143165)
                    ·
                      refine ⟨4164228492716402580428687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104609313910406881143165 4164228492716402580428687)
                      ·
                        rfl

theorem cell23_8109806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_8109806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109806 prefixEnd_8109806 := by exact prefixLift 8109806
  have htrace : WordTrace (prefixWord ++ tailWord_8109806) baseStart_8109806 baseEnd_8109806 := by
    simpa [prefixWord, tailWord_8109806, baseEnd_8109806] using wordTrace_append hprefix tailTrace_8109806
  have hstable : (prefixWord ++ tailWord_8109806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109806).length < 2 ^ (prefixWord ++ tailWord_8109806).sum := by decide
  have hdescent : baseEnd_8109806 < baseStart_8109806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109809 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_8109809 : Nat := 118140960795 + 8109809 * 2 ^ 59
def prefixEnd_8109809 : Nat := 4983230072969 + 3 ^ 40 * 8109809 * 2
def baseEnd_8109809 : Nat := 1388076677719455356230391

theorem tailTrace_8109809 : CollatzResearch.WordTrace tailWord_8109809 prefixEnd_8109809 1388076677719455356230391 := by
  unfold tailWord_8109809
  simp only [CollatzResearch.WordTrace]
  refine ⟨295789034276554512953236481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197192689517703008635490987 295789034276554512953236481)
  ·
    refine ⟨221841775707415884714927361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295789034276554512953236481 221841775707415884714927361)
    ·
      refine ⟨166381331780561913536195521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221841775707415884714927361 166381331780561913536195521)
      ·
        refine ⟨124785998835421435152146641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166381331780561913536195521 124785998835421435152146641)
        ·
          refine ⟨93589499126566076364109981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124785998835421435152146641 93589499126566076364109981)
          ·
            refine ⟨35096062172462278636541243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93589499126566076364109981 35096062172462278636541243)
            ·
              refine ⟨52644093258693417954811865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35096062172462278636541243 52644093258693417954811865)
              ·
                refine ⟨39483069944020063466108899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52644093258693417954811865 39483069944020063466108899)
                ·
                  refine ⟨59224604916030095199163349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39483069944020063466108899 59224604916030095199163349)
                  ·
                    refine ⟨1388076677719455356230391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59224604916030095199163349 1388076677719455356230391)
                    ·
                      rfl

theorem cell23_8109809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_8109809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109809 prefixEnd_8109809 := by exact prefixLift 8109809
  have htrace : WordTrace (prefixWord ++ tailWord_8109809) baseStart_8109809 baseEnd_8109809 := by
    simpa [prefixWord, tailWord_8109809, baseEnd_8109809] using wordTrace_append hprefix tailTrace_8109809
  have hstable : (prefixWord ++ tailWord_8109809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109809).length < 2 ^ (prefixWord ++ tailWord_8109809).sum := by decide
  have hdescent : baseEnd_8109809 < baseStart_8109809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109826 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8109826 : Nat := 118140960795 + 8109826 * 2 ^ 59
def prefixEnd_8109826 : Nat := 4983230072969 + 3 ^ 40 * 8109826 * 2
def baseEnd_8109826 : Nat := 1388079587443164167392865

theorem tailTrace_8109826 : CollatzResearch.WordTrace tailWord_8109826 prefixEnd_8109826 1388079587443164167392865 := by
  unfold tailWord_8109826
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947413579373231214151333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197193102878328616571070221 73947413579373231214151333)
  ·
    refine ⟨13865140046132480852653375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73947413579373231214151333 13865140046132480852653375)
    ·
      refine ⟨20797710069198721278980063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13865140046132480852653375 20797710069198721278980063)
      ·
        refine ⟨31196565103798081918470095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797710069198721278980063 31196565103798081918470095)
        ·
          refine ⟨46794847655697122877705143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31196565103798081918470095 46794847655697122877705143)
          ·
            refine ⟨70192271483545684316557715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46794847655697122877705143 70192271483545684316557715)
            ·
              refine ⟨105288407225318526474836573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70192271483545684316557715 105288407225318526474836573)
              ·
                refine ⟨39483152709494447428063715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105288407225318526474836573 39483152709494447428063715)
                ·
                  refine ⟨59224729064241671142095573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39483152709494447428063715 59224729064241671142095573)
                  ·
                    refine ⟨1388079587443164167392865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59224729064241671142095573 1388079587443164167392865)
                    ·
                      rfl

theorem cell23_8109826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8109826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109826 prefixEnd_8109826 := by exact prefixLift 8109826
  have htrace : WordTrace (prefixWord ++ tailWord_8109826) baseStart_8109826 baseEnd_8109826 := by
    simpa [prefixWord, tailWord_8109826, baseEnd_8109826] using wordTrace_append hprefix tailTrace_8109826
  have hstable : (prefixWord ++ tailWord_8109826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109826).length < 2 ^ (prefixWord ++ tailWord_8109826).sum := by decide
  have hdescent : baseEnd_8109826 < baseStart_8109826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109859 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_8109859 : Nat := 118140960795 + 8109859 * 2 ^ 59
def prefixEnd_8109859 : Nat := 4983230072969 + 3 ^ 40 * 8109859 * 2
def baseEnd_8109859 : Nat := 4164255707191090873065943

theorem tailTrace_8109859 : CollatzResearch.WordTrace tailWord_8109859 prefixEnd_8109859 4164255707191090873065943 := by
  unfold tailWord_8109859
  simp only [CollatzResearch.WordTrace]
  refine ⟨295790857926373371492556631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197193905284248914328371087 295790857926373371492556631)
  ·
    refine ⟨443686286889560057238834947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295790857926373371492556631 443686286889560057238834947)
    ·
      refine ⟨665529430334340085858252421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443686286889560057238834947 665529430334340085858252421)
      ·
        refine ⟨124786768187688766098422329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665529430334340085858252421 124786768187688766098422329)
        ·
          refine ⟨93590076140766574573816747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124786768187688766098422329 93590076140766574573816747)
          ·
            refine ⟨140385114211149861860725121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93590076140766574573816747 140385114211149861860725121)
            ·
              refine ⟨105288835658362396395543841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140385114211149861860725121 105288835658362396395543841)
              ·
                refine ⟨78966626743771797296657881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105288835658362396395543841 78966626743771797296657881)
                ·
                  refine ⟨59224970057828847972493411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78966626743771797296657881 59224970057828847972493411)
                  ·
                    refine ⟨88837455086743271958740117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59224970057828847972493411 88837455086743271958740117)
                    ·
                      refine ⟨4164255707191090873065943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88837455086743271958740117 4164255707191090873065943)
                      ·
                        rfl

theorem cell23_8109859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_8109859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109859 prefixEnd_8109859 := by exact prefixLift 8109859
  have htrace : WordTrace (prefixWord ++ tailWord_8109859) baseStart_8109859 baseEnd_8109859 := by
    simpa [prefixWord, tailWord_8109859, baseEnd_8109859] using wordTrace_append hprefix tailTrace_8109859
  have hstable : (prefixWord ++ tailWord_8109859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109859).length < 2 ^ (prefixWord ++ tailWord_8109859).sum := by decide
  have hdescent : baseEnd_8109859 < baseStart_8109859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109913 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_8109913 : Nat := 118140960795 + 8109913 * 2 ^ 59
def prefixEnd_8109913 : Nat := 4983230072969 + 3 ^ 40 * 8109913 * 2
def baseEnd_8109913 : Nat := 4164283435146433661790695

theorem tailTrace_8109913 : CollatzResearch.WordTrace tailWord_8109913 prefixEnd_8109913 4164283435146433661790695 := by
  unfold tailWord_8109913
  simp only [CollatzResearch.WordTrace]
  refine ⟨295792827468177738715022393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197195218312118492476681595 295792827468177738715022393)
  ·
    refine ⟨221844620601133304036266795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295792827468177738715022393 221844620601133304036266795)
    ·
      refine ⟨332766930901699956054400193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221844620601133304036266795 332766930901699956054400193)
      ·
        refine ⟨249575198176274967040800145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332766930901699956054400193 249575198176274967040800145)
        ·
          refine ⟨187181398632206225280600109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249575198176274967040800145 187181398632206225280600109)
          ·
            refine ⟨70193024487077334480225041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187181398632206225280600109 70193024487077334480225041)
            ·
              refine ⟨52644768365308000860168781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70193024487077334480225041 52644768365308000860168781)
              ·
                refine ⟨19741788136990500322563293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52644768365308000860168781 19741788136990500322563293)
                ·
                  refine ⟨7403170551371437620961235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19741788136990500322563293 7403170551371437620961235)
                  ·
                    refine ⟨11104755827057156431441853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403170551371437620961235 11104755827057156431441853)
                    ·
                      refine ⟨4164283435146433661790695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104755827057156431441853 4164283435146433661790695)
                      ·
                        rfl

theorem cell23_8109913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_8109913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109913 prefixEnd_8109913 := by exact prefixLift 8109913
  have htrace : WordTrace (prefixWord ++ tailWord_8109913) baseStart_8109913 baseEnd_8109913 := by
    simpa [prefixWord, tailWord_8109913, baseEnd_8109913] using wordTrace_append hprefix tailTrace_8109913
  have hstable : (prefixWord ++ tailWord_8109913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109913).length < 2 ^ (prefixWord ++ tailWord_8109913).sum := by decide
  have hdescent : baseEnd_8109913 < baseStart_8109913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109946 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_8109946 : Nat := 118140960795 + 8109946 * 2 ^ 59
def prefixEnd_8109946 : Nat := 4983230072969 + 3 ^ 40 * 8109946 * 2
def baseEnd_8109946 : Nat := 1388100126669344010892681

theorem tailTrace_8109946 : CollatzResearch.WordTrace tailWord_8109946 prefixEnd_8109946 1388100126669344010892681 := by
  unfold tailWord_8109946
  simp only [CollatzResearch.WordTrace]
  refine ⟨73948507769264546337743423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197196020718038790233982461 73948507769264546337743423)
  ·
    refine ⟨110922761653896819506615135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73948507769264546337743423 110922761653896819506615135)
    ·
      refine ⟨166384142480845229259922703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110922761653896819506615135 166384142480845229259922703)
      ·
        refine ⟨249576213721267843889884055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166384142480845229259922703 249576213721267843889884055)
        ·
          refine ⟨374364320581901765834826083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249576213721267843889884055 374364320581901765834826083)
          ·
            refine ⟨561546480872852648752239125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374364320581901765834826083 561546480872852648752239125)
            ·
              refine ⟨26322491290914967910261209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561546480872852648752239125 26322491290914967910261209)
              ·
                refine ⟨19741868468186225932695907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26322491290914967910261209 19741868468186225932695907)
                ·
                  refine ⟨29612802702279338899043861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741868468186225932695907 29612802702279338899043861)
                  ·
                    refine ⟨1388100126669344010892681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29612802702279338899043861 1388100126669344010892681)
                    ·
                      rfl

theorem cell23_8109946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_8109946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109946 prefixEnd_8109946 := by exact prefixLift 8109946
  have htrace : WordTrace (prefixWord ++ tailWord_8109946) baseStart_8109946 baseEnd_8109946 := by
    simpa [prefixWord, tailWord_8109946, baseEnd_8109946] using wordTrace_append hprefix tailTrace_8109946
  have hstable : (prefixWord ++ tailWord_8109946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109946).length < 2 ^ (prefixWord ++ tailWord_8109946).sum := by decide
  have hdescent : baseEnd_8109946 < baseStart_8109946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109980 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_8109980 : Nat := 118140960795 + 8109980 * 2 ^ 59
def prefixEnd_8109980 : Nat := 4983230072969 + 3 ^ 40 * 8109980 * 2
def baseEnd_8109980 : Nat := 1388105946116761633217629

theorem tailTrace_8109980 : CollatzResearch.WordTrace tailWord_8109980 prefixEnd_8109980 1388105946116761633217629 := by
  unfold tailWord_8109980
  simp only [CollatzResearch.WordTrace]
  refine ⟨147897635579467504578855697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197196847439290006105140929 147897635579467504578855697)
  ·
    refine ⟨110923226684600628434141773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147897635579467504578855697 110923226684600628434141773)
    ·
      refine ⟨41596210006725235662803165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110923226684600628434141773 41596210006725235662803165)
      ·
        refine ⟨15598578752521963373551187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41596210006725235662803165 15598578752521963373551187)
        ·
          refine ⟨23397868128782945060326781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598578752521963373551187 23397868128782945060326781)
          ·
            refine ⟨8774200548293604397622543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23397868128782945060326781 8774200548293604397622543)
            ·
              refine ⟨13161300822440406596433815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774200548293604397622543 13161300822440406596433815)
              ·
                refine ⟨19741951233660609894650723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13161300822440406596433815 19741951233660609894650723)
                ·
                  refine ⟨29612926850490914841976085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741951233660609894650723 29612926850490914841976085)
                  ·
                    refine ⟨1388105946116761633217629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29612926850490914841976085 1388105946116761633217629)
                    ·
                      rfl

theorem cell23_8109980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_8109980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109980 prefixEnd_8109980 := by exact prefixLift 8109980
  have htrace : WordTrace (prefixWord ++ tailWord_8109980) baseStart_8109980 baseEnd_8109980 := by
    simpa [prefixWord, tailWord_8109980, baseEnd_8109980] using wordTrace_append hprefix tailTrace_8109980
  have hstable : (prefixWord ++ tailWord_8109980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109980).length < 2 ^ (prefixWord ++ tailWord_8109980).sum := by decide
  have hdescent : baseEnd_8109980 < baseStart_8109980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8109983 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6]
def baseStart_8109983 : Nat := 118140960795 + 8109983 * 2 ^ 59
def prefixEnd_8109983 : Nat := 4983230072969 + 3 ^ 40 * 8109983 * 2
def baseEnd_8109983 : Nat := 4164319378792248387915373

theorem tailTrace_8109983 : CollatzResearch.WordTrace tailWord_8109983 prefixEnd_8109983 4164319378792248387915373 := by
  unfold tailWord_8109983
  simp only [CollatzResearch.WordTrace]
  refine ⟨295795380577924140670070603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197196920385282760446713735 295795380577924140670070603)
  ·
    refine ⟨443693070866886211005105905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295795380577924140670070603 443693070866886211005105905)
    ·
      refine ⟨332769803150164658253829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443693070866886211005105905 332769803150164658253829429)
      ·
        refine ⟨31197169045327936711296509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332769803150164658253829429 31197169045327936711296509)
        ·
          refine ⟨11698938391997976266736191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31197169045327936711296509 11698938391997976266736191)
          ·
            refine ⟨17548407587996964400104287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698938391997976266736191 17548407587996964400104287)
            ·
              refine ⟨26322611381995446600156431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548407587996964400104287 26322611381995446600156431)
              ·
                refine ⟨39483917072993169900234647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26322611381995446600156431 39483917072993169900234647)
                ·
                  refine ⟨59225875609489754850351971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39483917072993169900234647 59225875609489754850351971)
                  ·
                    refine ⟨88838813414234632275527957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59225875609489754850351971 88838813414234632275527957)
                    ·
                      refine ⟨4164319378792248387915373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88838813414234632275527957 4164319378792248387915373)
                      ·
                        rfl

theorem cell23_8109983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_8109983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8109983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8109983 prefixEnd_8109983 := by exact prefixLift 8109983
  have htrace : WordTrace (prefixWord ++ tailWord_8109983) baseStart_8109983 baseEnd_8109983 := by
    simpa [prefixWord, tailWord_8109983, baseEnd_8109983] using wordTrace_append hprefix tailTrace_8109983
  have hstable : (prefixWord ++ tailWord_8109983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8109983).length < 2 ^ (prefixWord ++ tailWord_8109983).sum := by decide
  have hdescent : baseEnd_8109983 < baseStart_8109983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8109983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110003 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 3]
def baseStart_8110003 : Nat := 118140960795 + 8110003 * 2 ^ 59
def prefixEnd_8110003 : Nat := 4983230072969 + 3 ^ 40 * 8110003 * 2
def baseEnd_8110003 : Nat := 4164329648405338309665281

theorem tailTrace_8110003 : CollatzResearch.WordTrace tailWord_8110003 prefixEnd_8110003 4164329648405338309665281 := by
  unfold tailWord_8110003
  simp only [CollatzResearch.WordTrace]
  refine ⟨295796110037851684085798663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197197406691901122723865775 295796110037851684085798663)
  ·
    refine ⟨443694165056777526128697995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295796110037851684085798663 443694165056777526128697995)
    ·
      refine ⟨665541247585166289193046993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443694165056777526128697995 665541247585166289193046993)
      ·
        refine ⟨499155935688874716894785245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665541247585166289193046993 499155935688874716894785245)
        ·
          refine ⟨187183475883328018835544467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499155935688874716894785245 187183475883328018835544467)
          ·
            refine ⟨280775213824992028253316701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187183475883328018835544467 280775213824992028253316701)
            ·
              refine ⟨105290705184372010594993763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280775213824992028253316701 105290705184372010594993763)
              ·
                refine ⟨157936057776558015892490645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105290705184372010594993763 157936057776558015892490645)
                ·
                  refine ⟨7403252708276156994960499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157936057776558015892490645 7403252708276156994960499)
                  ·
                    refine ⟨11104879062414235492440749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403252708276156994960499 11104879062414235492440749)
                    ·
                      refine ⟨4164329648405338309665281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104879062414235492440749 4164329648405338309665281)
                      ·
                        rfl

theorem cell23_8110003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_8110003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110003 prefixEnd_8110003 := by exact prefixLift 8110003
  have htrace : WordTrace (prefixWord ++ tailWord_8110003) baseStart_8110003 baseEnd_8110003 := by
    simpa [prefixWord, tailWord_8110003, baseEnd_8110003] using wordTrace_append hprefix tailTrace_8110003
  have hstable : (prefixWord ++ tailWord_8110003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110003).length < 2 ^ (prefixWord ++ tailWord_8110003).sum := by decide
  have hdescent : baseEnd_8110003 < baseStart_8110003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110016 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_8110016 : Nat := 118140960795 + 8110016 * 2 ^ 59
def prefixEnd_8110016 : Nat := 4983230072969 + 3 ^ 40 * 8110016 * 2
def baseEnd_8110016 : Nat := 4164336323653846758802721

theorem tailTrace_8110016 : CollatzResearch.WordTrace tailWord_8110016 prefixEnd_8110016 4164336323653846758802721 := by
  unfold tailWord_8110016
  simp only [CollatzResearch.WordTrace]
  refine ⟨147898292093402293653010951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197197722791203058204014601 147898292093402293653010951)
  ·
    refine ⟨221847438140103440479516427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147898292093402293653010951 221847438140103440479516427)
    ·
      refine ⟨332771157210155160719274641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221847438140103440479516427 332771157210155160719274641)
      ·
        refine ⟨249578367907616370539455981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332771157210155160719274641 249578367907616370539455981)
        ·
          refine ⟨93591887965356138952295993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249578367907616370539455981 93591887965356138952295993)
          ·
            refine ⟨70193915974017104214221995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93591887965356138952295993 70193915974017104214221995)
            ·
              refine ⟨105290873961025656321332993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70193915974017104214221995 105290873961025656321332993)
              ·
                refine ⟨78968155470769242240999745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105290873961025656321332993 78968155470769242240999745)
                ·
                  refine ⟨59226116603076931680749809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78968155470769242240999745 59226116603076931680749809)
                  ·
                    refine ⟨44419587452307698760562357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59226116603076931680749809 44419587452307698760562357)
                    ·
                      refine ⟨4164336323653846758802721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44419587452307698760562357 4164336323653846758802721)
                      ·
                        rfl

theorem cell23_8110016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_8110016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110016 prefixEnd_8110016 := by exact prefixLift 8110016
  have htrace : WordTrace (prefixWord ++ tailWord_8110016) baseStart_8110016 baseEnd_8110016 := by
    simpa [prefixWord, tailWord_8110016, baseEnd_8110016] using wordTrace_append hprefix tailTrace_8110016
  have hstable : (prefixWord ++ tailWord_8110016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110016).length < 2 ^ (prefixWord ++ tailWord_8110016).sum := by decide
  have hdescent : baseEnd_8110016 < baseStart_8110016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110030 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_8110030 : Nat := 118140960795 + 8110030 * 2 ^ 59
def prefixEnd_8110030 : Nat := 4983230072969 + 3 ^ 40 * 8110030 * 2
def baseEnd_8110030 : Nat := 4164343512383009704027657

theorem tailTrace_8110030 : CollatzResearch.WordTrace tailWord_8110030 prefixEnd_8110030 4164343512383009704027657 := by
  unfold tailWord_8110030
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974636851094233462128943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197198063205835911798021029 36974636851094233462128943)
  ·
    refine ⟨55461955276641350193193415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36974636851094233462128943 55461955276641350193193415)
    ·
      refine ⟨83192932914962025289790123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55461955276641350193193415 83192932914962025289790123)
      ·
        refine ⟨124789399372443037934685185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83192932914962025289790123 124789399372443037934685185)
        ·
          refine ⟨93592049529332278451013889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124789399372443037934685185 93592049529332278451013889)
          ·
            refine ⟨70194037146999208838260417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93592049529332278451013889 70194037146999208838260417)
            ·
              refine ⟨52645527860249406628695313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70194037146999208838260417 52645527860249406628695313)
              ·
                refine ⟨39484145895187054971521485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52645527860249406628695313 39484145895187054971521485)
                ·
                  refine ⟨14806554710695145614320557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39484145895187054971521485 14806554710695145614320557)
                  ·
                    refine ⟨5552458016510679605370209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14806554710695145614320557 5552458016510679605370209)
                    ·
                      refine ⟨4164343512383009704027657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552458016510679605370209 4164343512383009704027657)
                      ·
                        rfl

theorem cell23_8110030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_8110030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110030 prefixEnd_8110030 := by exact prefixLift 8110030
  have htrace : WordTrace (prefixWord ++ tailWord_8110030) baseStart_8110030 baseEnd_8110030 := by
    simpa [prefixWord, tailWord_8110030, baseEnd_8110030] using wordTrace_append hprefix tailTrace_8110030
  have hstable : (prefixWord ++ tailWord_8110030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110030).length < 2 ^ (prefixWord ++ tailWord_8110030).sum := by decide
  have hdescent : baseEnd_8110030 < baseStart_8110030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110037 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_8110037 : Nat := 118140960795 + 8110037 * 2 ^ 59
def prefixEnd_8110037 : Nat := 4983230072969 + 3 ^ 40 * 8110037 * 2
def baseEnd_8110037 : Nat := 4164347106747591176640125

theorem tailTrace_8110037 : CollatzResearch.WordTrace tailWord_8110037 prefixEnd_8110037 4164347106747591176640125 := by
  unfold tailWord_8110037
  simp only [CollatzResearch.WordTrace]
  refine ⟨295797350119728507892536365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197198233413152338595024243 295797350119728507892536365)
  ·
    refine ⟨110924006294898190459701137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295797350119728507892536365 110924006294898190459701137)
    ·
      refine ⟨83193004721173642844775853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110924006294898190459701137 83193004721173642844775853)
      ·
        refine ⟨31197376770440116066790945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83193004721173642844775853 31197376770440116066790945)
        ·
          refine ⟨23398032577830087050093209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31197376770440116066790945 23398032577830087050093209)
          ·
            refine ⟨17548524433372565287569907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23398032577830087050093209 17548524433372565287569907)
            ·
              refine ⟨26322786650058847931354861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548524433372565287569907 26322786650058847931354861)
              ·
                refine ⟨9871044993772067974258073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26322786650058847931354861 9871044993772067974258073)
                ·
                  refine ⟨7403283745329050980693555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871044993772067974258073 7403283745329050980693555)
                  ·
                    refine ⟨11104925617993576471040333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403283745329050980693555 11104925617993576471040333)
                    ·
                      refine ⟨4164347106747591176640125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11104925617993576471040333 4164347106747591176640125)
                      ·
                        rfl

theorem cell23_8110037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_8110037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110037 prefixEnd_8110037 := by exact prefixLift 8110037
  have htrace : WordTrace (prefixWord ++ tailWord_8110037) baseStart_8110037 baseEnd_8110037 := by
    simpa [prefixWord, tailWord_8110037, baseEnd_8110037] using wordTrace_append hprefix tailTrace_8110037
  have hstable : (prefixWord ++ tailWord_8110037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110037).length < 2 ^ (prefixWord ++ tailWord_8110037).sum := by decide
  have hdescent : baseEnd_8110037 < baseStart_8110037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110047 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 1, 3, 2]
def baseStart_8110047 : Nat := 118140960795 + 8110047 * 2 ^ 59
def prefixEnd_8110047 : Nat := 4983230072969 + 3 ^ 40 * 8110047 * 2
def baseEnd_8110047 : Nat := 4164352241554136137515079

theorem tailTrace_8110047 : CollatzResearch.WordTrace tailWord_8110047 prefixEnd_8110047 4164352241554136137515079 := by
  unfold tailWord_8110047
  simp only [CollatzResearch.WordTrace]
  refine ⟨295797714849692279600400395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197198476566461519733600263 295797714849692279600400395)
  ·
    refine ⟨443696572274538419400600593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295797714849692279600400395 443696572274538419400600593)
    ·
      refine ⟨332772429205903814550450445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443696572274538419400600593 332772429205903814550450445)
      ·
        refine ⟨124789660952213930456418917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332772429205903814550450445 124789660952213930456418917)
        ·
          refine ⟨23398061428540111960578547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124789660952213930456418917 23398061428540111960578547)
          ·
            refine ⟨35097092142810167940867821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23398061428540111960578547 35097092142810167940867821)
            ·
              refine ⟨13161409553553812977825433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35097092142810167940867821 13161409553553812977825433)
              ·
                refine ⟨9871057165165359733369075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13161409553553812977825433 9871057165165359733369075)
                ·
                  refine ⟨14806585747748039600053613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9871057165165359733369075 14806585747748039600053613)
                  ·
                    refine ⟨5552469655405514850020105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14806585747748039600053613 5552469655405514850020105)
                    ·
                      refine ⟨4164352241554136137515079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552469655405514850020105 4164352241554136137515079)
                      ·
                        rfl

theorem cell23_8110047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_8110047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110047 prefixEnd_8110047 := by exact prefixLift 8110047
  have htrace : WordTrace (prefixWord ++ tailWord_8110047) baseStart_8110047 baseEnd_8110047 := by
    simpa [prefixWord, tailWord_8110047, baseEnd_8110047] using wordTrace_append hprefix tailTrace_8110047
  have hstable : (prefixWord ++ tailWord_8110047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110047).length < 2 ^ (prefixWord ++ tailWord_8110047).sum := by decide
  have hdescent : baseEnd_8110047 < baseStart_8110047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110060 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_8110060 : Nat := 118140960795 + 8110060 * 2 ^ 59
def prefixEnd_8110060 : Nat := 4983230072969 + 3 ^ 40 * 8110060 * 2
def baseEnd_8110060 : Nat := 4164358916802644586652519

theorem tailTrace_8110060 : CollatzResearch.WordTrace tailWord_8110060 prefixEnd_8110060 4164358916802644586652519 := by
  unfold tailWord_8110060
  simp only [CollatzResearch.WordTrace]
  refine ⟨147899094499322591410311817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197198792665763455213749089 147899094499322591410311817)
  ·
    refine ⟨110924320874491943557733863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147899094499322591410311817 110924320874491943557733863)
    ·
      refine ⟨166386481311737915336600795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110924320874491943557733863 166386481311737915336600795)
      ·
        refine ⟨249579721967606873004901193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166386481311737915336600795 249579721967606873004901193)
        ·
          refine ⟨187184791475705154753675895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249579721967606873004901193 187184791475705154753675895)
          ·
            refine ⟨280777187213557732130513843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187184791475705154753675895 280777187213557732130513843)
            ·
              refine ⟨421165780820336598195770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280777187213557732130513843 421165780820336598195770765)
              ·
                refine ⟨157937167807626224323414037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421165780820336598195770765 157937167807626224323414037)
                ·
                  refine ⟨7403304740982479265160033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157937167807626224323414037 7403304740982479265160033)
                  ·
                    refine ⟨5552478555736859448870025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403304740982479265160033 5552478555736859448870025)
                    ·
                      refine ⟨4164358916802644586652519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552478555736859448870025 4164358916802644586652519)
                      ·
                        rfl

theorem cell23_8110060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_8110060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110060 prefixEnd_8110060 := by exact prefixLift 8110060
  have htrace : WordTrace (prefixWord ++ tailWord_8110060) baseStart_8110060 baseEnd_8110060 := by
    simpa [prefixWord, tailWord_8110060, baseEnd_8110060] using wordTrace_append hprefix tailTrace_8110060
  have hstable : (prefixWord ++ tailWord_8110060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110060).length < 2 ^ (prefixWord ++ tailWord_8110060).sum := by decide
  have hdescent : baseEnd_8110060 < baseStart_8110060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110077 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_8110077 : Nat := 118140960795 + 8110077 * 2 ^ 59
def prefixEnd_8110077 : Nat := 4983230072969 + 3 ^ 40 * 8110077 * 2
def baseEnd_8110077 : Nat := 4164367645973771020139941

theorem tailTrace_8110077 : CollatzResearch.WordTrace tailWord_8110077 prefixEnd_8110077 4164367645973771020139941 := by
  unfold tailWord_8110077
  simp only [CollatzResearch.WordTrace]
  refine ⟨295798809039583594723992485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197199206026389063149328323 295798809039583594723992485)
  ·
    refine ⟨55462276694921924010748591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295798809039583594723992485 55462276694921924010748591)
    ·
      refine ⟨83193415042382886016122887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55462276694921924010748591 83193415042382886016122887)
      ·
        refine ⟨124790122563574329024184331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83193415042382886016122887 124790122563574329024184331)
        ·
          refine ⟨187185183845361493536276497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124790122563574329024184331 187185183845361493536276497)
          ·
            refine ⟨140388887884021120152207373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187185183845361493536276497 140388887884021120152207373)
            ·
              refine ⟨52645832956507920057077765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140388887884021120152207373 52645832956507920057077765)
              ·
                refine ⟨9871093679345235010702081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52645832956507920057077765 9871093679345235010702081)
                ·
                  refine ⟨7403320259508926258026561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871093679345235010702081 7403320259508926258026561)
                  ·
                    refine ⟨5552490194631694693519921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403320259508926258026561 5552490194631694693519921)
                    ·
                      refine ⟨4164367645973771020139941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552490194631694693519921 4164367645973771020139941)
                      ·
                        rfl

theorem cell23_8110077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_8110077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110077 prefixEnd_8110077 := by exact prefixLift 8110077
  have htrace : WordTrace (prefixWord ++ tailWord_8110077) baseStart_8110077 baseEnd_8110077 := by
    simpa [prefixWord, tailWord_8110077, baseEnd_8110077] using wordTrace_append hprefix tailTrace_8110077
  have hstable : (prefixWord ++ tailWord_8110077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110077).length < 2 ^ (prefixWord ++ tailWord_8110077).sum := by decide
  have hdescent : baseEnd_8110077 < baseStart_8110077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110090 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_8110090 : Nat := 118140960795 + 8110090 * 2 ^ 59
def prefixEnd_8110090 : Nat := 4983230072969 + 3 ^ 40 * 8110090 * 2
def baseEnd_8110090 : Nat := 4164374321222279469277381

theorem tailTrace_8110090 : CollatzResearch.WordTrace tailWord_8110090 prefixEnd_8110090 4164374321222279469277381 := by
  unfold tailWord_8110090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73949820797134124486053931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197199522125690998629477149 73949820797134124486053931)
  ·
    refine ⟨110924731195701186729080897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73949820797134124486053931 110924731195701186729080897)
    ·
      refine ⟨83193548396775890046810673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110924731195701186729080897 83193548396775890046810673)
      ·
        refine ⟨62395161297581917535108005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83193548396775890046810673 62395161297581917535108005)
        ·
          refine ⟨11699092743296609537832751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62395161297581917535108005 11699092743296609537832751)
          ·
            refine ⟨17548639114944914306749127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11699092743296609537832751 17548639114944914306749127)
            ·
              refine ⟨26322958672417371460123691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548639114944914306749127 26322958672417371460123691)
              ·
                refine ⟨39484438008626057190185537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26322958672417371460123691 39484438008626057190185537)
                ·
                  refine ⟨29613328506469542892639153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39484438008626057190185537 29613328506469542892639153)
                  ·
                    refine ⟨22209996379852157169479365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29613328506469542892639153 22209996379852157169479365)
                    ·
                      refine ⟨4164374321222279469277381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22209996379852157169479365 4164374321222279469277381)
                      ·
                        rfl

theorem cell23_8110090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_8110090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110090 prefixEnd_8110090 := by exact prefixLift 8110090
  have htrace : WordTrace (prefixWord ++ tailWord_8110090) baseStart_8110090 baseEnd_8110090 := by
    simpa [prefixWord, tailWord_8110090, baseEnd_8110090] using wordTrace_append hprefix tailTrace_8110090
  have hstable : (prefixWord ++ tailWord_8110090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110090).length < 2 ^ (prefixWord ++ tailWord_8110090).sum := by decide
  have hdescent : baseEnd_8110090 < baseStart_8110090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110096 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_8110096 : Nat := 118140960795 + 8110096 * 2 ^ 59
def prefixEnd_8110096 : Nat := 4983230072969 + 3 ^ 40 * 8110096 * 2
def baseEnd_8110096 : Nat := 1388125800702068815267451

theorem tailTrace_8110096 : CollatzResearch.WordTrace tailWord_8110096 prefixEnd_8110096 1388125800702068815267451 := by
  unfold tailWord_8110096
  simp only [CollatzResearch.WordTrace]
  refine ⟨147899751013257380484467071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197199668017676507312622761 147899751013257380484467071)
  ·
    refine ⟨221849626519886070726700607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147899751013257380484467071 221849626519886070726700607)
    ·
      refine ⟨332774439779829106090050911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221849626519886070726700607 332774439779829106090050911)
      ·
        refine ⟨499161659669743659135076367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332774439779829106090050911 499161659669743659135076367)
        ·
          refine ⟨748742489504615488702614551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499161659669743659135076367 748742489504615488702614551)
          ·
            refine ⟨1123113734256923233053921827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748742489504615488702614551 1123113734256923233053921827)
            ·
              refine ⟨1684670601385384849580882741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123113734256923233053921827 1684670601385384849580882741)
              ·
                refine ⟨157937868879879829648207757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1684670601385384849580882741 157937868879879829648207757)
                ·
                  refine ⟨59226700829954936118077909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157937868879879829648207757 59226700829954936118077909)
                  ·
                    refine ⟨1388125800702068815267451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59226700829954936118077909 1388125800702068815267451)
                    ·
                      rfl

theorem cell23_8110096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_8110096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110096 prefixEnd_8110096 := by exact prefixLift 8110096
  have htrace : WordTrace (prefixWord ++ tailWord_8110096) baseStart_8110096 baseEnd_8110096 := by
    simpa [prefixWord, tailWord_8110096, baseEnd_8110096] using wordTrace_append hprefix tailTrace_8110096
  have hstable : (prefixWord ++ tailWord_8110096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110096).length < 2 ^ (prefixWord ++ tailWord_8110096).sum := by decide
  have hdescent : baseEnd_8110096 < baseStart_8110096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110153 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_8110153 : Nat := 118140960795 + 8110153 * 2 ^ 59
def prefixEnd_8110153 : Nat := 4983230072969 + 3 ^ 40 * 8110153 * 2
def baseEnd_8110153 : Nat := 4164406670503512722789591

theorem tailTrace_8110153 : CollatzResearch.WordTrace tailWord_8110153 prefixEnd_8110153 4164406670503512722789591 := by
  unfold tailWord_8110153
  simp only [CollatzResearch.WordTrace]
  refine ⟨295801580987308259703759113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197201053991538839802506075 295801580987308259703759113)
  ·
    refine ⟨221851185740481194777819335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295801580987308259703759113 221851185740481194777819335)
    ·
      refine ⟨332776778610721792166729003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221851185740481194777819335 332776778610721792166729003)
      ·
        refine ⟨499165167916082688250093505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332776778610721792166729003 499165167916082688250093505)
        ·
          refine ⟨374373875937062016187570129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499165167916082688250093505 374373875937062016187570129)
          ·
            refine ⟨280780406952796512140677597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374373875937062016187570129 280780406952796512140677597)
            ·
              refine ⟨105292652607298692052754099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280780406952796512140677597 105292652607298692052754099)
              ·
                refine ⟨157938978910948038079131149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105292652607298692052754099 157938978910948038079131149)
                ·
                  refine ⟨59227117091605514279674181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157938978910948038079131149 59227117091605514279674181)
                  ·
                    refine ⟨11105084454676033927438909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59227117091605514279674181 11105084454676033927438909)
                    ·
                      refine ⟨4164406670503512722789591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11105084454676033927438909 4164406670503512722789591)
                      ·
                        rfl

theorem cell23_8110153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_8110153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110153 prefixEnd_8110153 := by exact prefixLift 8110153
  have htrace : WordTrace (prefixWord ++ tailWord_8110153) baseStart_8110153 baseEnd_8110153 := by
    simpa [prefixWord, tailWord_8110153, baseEnd_8110153] using wordTrace_append hprefix tailTrace_8110153
  have hstable : (prefixWord ++ tailWord_8110153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110153).length < 2 ^ (prefixWord ++ tailWord_8110153).sum := by decide
  have hdescent : baseEnd_8110153 < baseStart_8110153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110170 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_8110170 : Nat := 118140960795 + 8110170 * 2 ^ 59
def prefixEnd_8110170 : Nat := 4983230072969 + 3 ^ 40 * 8110170 * 2
def baseEnd_8110170 : Nat := 4164415399674639156277013

theorem tailTrace_8110170 : CollatzResearch.WordTrace tailWord_8110170 prefixEnd_8110170 4164415399674639156277013 := by
  unfold tailWord_8110170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73950550257061667901781991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197201467352164447738085309 73950550257061667901781991)
  ·
    refine ⟨110925825385592501852672987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73950550257061667901781991 110925825385592501852672987)
    ·
      refine ⟨166388738078388752779009481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110925825385592501852672987 166388738078388752779009481)
      ·
        refine ⟨124791553558791564584257111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166388738078388752779009481 124791553558791564584257111)
        ·
          refine ⟨187187330338187346876385667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124791553558791564584257111 187187330338187346876385667)
          ·
            refine ⟨280780995507281020314578501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187187330338187346876385667 280780995507281020314578501)
            ·
              refine ⟨52646436657615191308983469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280780995507281020314578501 52646436657615191308983469)
              ·
                refine ⟨19742413746605696740868801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52646436657615191308983469 19742413746605696740868801)
                ·
                  refine ⟨14806810309954272555651601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19742413746605696740868801 14806810309954272555651601)
                  ·
                    refine ⟨11105107732465704416738701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14806810309954272555651601 11105107732465704416738701)
                    ·
                      refine ⟨4164415399674639156277013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11105107732465704416738701 4164415399674639156277013)
                      ·
                        rfl

theorem cell23_8110170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_8110170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110170 prefixEnd_8110170 := by exact prefixLift 8110170
  have htrace : WordTrace (prefixWord ++ tailWord_8110170) baseStart_8110170 baseEnd_8110170 := by
    simpa [prefixWord, tailWord_8110170, baseEnd_8110170] using wordTrace_append hprefix tailTrace_8110170
  have hstable : (prefixWord ++ tailWord_8110170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110170).length < 2 ^ (prefixWord ++ tailWord_8110170).sum := by decide
  have hdescent : baseEnd_8110170 < baseStart_8110170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110190 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_8110190 : Nat := 118140960795 + 8110190 * 2 ^ 59
def prefixEnd_8110190 : Nat := 4983230072969 + 3 ^ 40 * 8110190 * 2
def baseEnd_8110190 : Nat := 462713963254192119780769

theorem tailTrace_8110190 : CollatzResearch.WordTrace tailWord_8110190 prefixEnd_8110190 462713963254192119780769 := by
  unfold tailWord_8110190
  simp only [CollatzResearch.WordTrace]
  refine ⟨36975366311021776877857003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197201953658782810015237349 36975366311021776877857003)
  ·
    refine ⟨55463049466532665316785505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36975366311021776877857003 55463049466532665316785505)
    ·
      refine ⟨41597287099899498987589129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55463049466532665316785505 41597287099899498987589129)
      ·
        refine ⟨31197965324924624240691847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41597287099899498987589129 31197965324924624240691847)
        ·
          refine ⟨46796947987386936361037771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31197965324924624240691847 46796947987386936361037771)
          ·
            refine ⟨70195421981080404541556657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46796947987386936361037771 70195421981080404541556657)
            ·
              refine ⟨52646566485810303406167493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70195421981080404541556657 52646566485810303406167493)
              ·
                refine ⟨9871231216089431888656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52646566485810303406167493 9871231216089431888656405)
                ·
                  refine ⟨462713963254192119780769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9871231216089431888656405 462713963254192119780769)
                  ·
                    rfl

theorem cell23_8110190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_8110190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110190 prefixEnd_8110190 := by exact prefixLift 8110190
  have htrace : WordTrace (prefixWord ++ tailWord_8110190) baseStart_8110190 baseEnd_8110190 := by
    simpa [prefixWord, tailWord_8110190, baseEnd_8110190] using wordTrace_append hprefix tailTrace_8110190
  have hstable : (prefixWord ++ tailWord_8110190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110190).length < 2 ^ (prefixWord ++ tailWord_8110190).sum := by decide
  have hdescent : baseEnd_8110190 < baseStart_8110190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110301 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_8110301 : Nat := 118140960795 + 8110301 * 2 ^ 59
def prefixEnd_8110301 : Nat := 4983230072969 + 3 ^ 40 * 8110301 * 2
def baseEnd_8110301 : Nat := 1388160888546792714579637

theorem tailTrace_8110301 : CollatzResearch.WordTrace tailWord_8110301 prefixEnd_8110301 1388160888546792714579637 := by
  unfold tailWord_8110301
  simp only [CollatzResearch.WordTrace]
  refine ⟨295806978990772080980146757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197204652660514720653431171 295806978990772080980146757)
  ·
    refine ⟨55463808560769765183777517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295806978990772080980146757 55463808560769765183777517)
    ·
      refine ⟨20798928210288661943916569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55463808560769765183777517 20798928210288661943916569)
      ·
        refine ⟨15599196157716496457937427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20798928210288661943916569 15599196157716496457937427)
        ·
          refine ⟨23398794236574744686906141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15599196157716496457937427 23398794236574744686906141)
          ·
            refine ⟨8774547838715529257589803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23398794236574744686906141 8774547838715529257589803)
            ·
              refine ⟨13161821758073293886384705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774547838715529257589803 13161821758073293886384705)
              ·
                refine ⟨9871366318554970414788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13161821758073293886384705 9871366318554970414788529)
                ·
                  refine ⟨7403524738916227811091397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871366318554970414788529 7403524738916227811091397)
                  ·
                    refine ⟨1388160888546792714579637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403524738916227811091397 1388160888546792714579637)
                    ·
                      rfl

theorem cell23_8110301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_8110301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110301 prefixEnd_8110301 := by exact prefixLift 8110301
  have htrace : WordTrace (prefixWord ++ tailWord_8110301) baseStart_8110301 baseEnd_8110301 := by
    simpa [prefixWord, tailWord_8110301, baseEnd_8110301] using wordTrace_append hprefix tailTrace_8110301
  have hstable : (prefixWord ++ tailWord_8110301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110301).length < 2 ^ (prefixWord ++ tailWord_8110301).sum := by decide
  have hdescent : baseEnd_8110301 < baseStart_8110301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110347 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 3, 4, 2]
def baseStart_8110347 : Nat := 118140960795 + 8110347 * 2 ^ 59
def prefixEnd_8110347 : Nat := 4983230072969 + 3 ^ 40 * 8110347 * 2
def baseEnd_8110347 : Nat := 4164506285750484963763699

theorem tailTrace_8110347 : CollatzResearch.WordTrace tailWord_8110347 prefixEnd_8110347 4164506285750484963763699 := by
  unfold tailWord_8110347
  simp only [CollatzResearch.WordTrace]
  refine ⟨295808656748605430836321295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197205771165736953890880863 295808656748605430836321295)
  ·
    refine ⟨443712985122908146254481943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295808656748605430836321295 443712985122908146254481943)
    ·
      refine ⟨665569477684362219381722915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443712985122908146254481943 665569477684362219381722915)
      ·
        refine ⟨998354216526543329072584373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665569477684362219381722915 998354216526543329072584373)
        ·
          refine ⟨93595707799363437100554785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 998354216526543329072584373 93595707799363437100554785)
          ·
            refine ⟨70196780849522577825416089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93595707799363437100554785 70196780849522577825416089)
            ·
              refine ⟨52647585637141933369062067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70196780849522577825416089 52647585637141933369062067)
              ·
                refine ⟨78971378455712900053593101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52647585637141933369062067 78971378455712900053593101)
                ·
                  refine ⟨29614266920892337520097413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78971378455712900053593101 29614266920892337520097413)
                  ·
                    refine ⟨5552675047667313285018265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29614266920892337520097413 5552675047667313285018265)
                    ·
                      refine ⟨4164506285750484963763699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552675047667313285018265 4164506285750484963763699)
                      ·
                        rfl

theorem cell23_8110347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4, 2].length) (baseStart_8110347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110347 prefixEnd_8110347 := by exact prefixLift 8110347
  have htrace : WordTrace (prefixWord ++ tailWord_8110347) baseStart_8110347 baseEnd_8110347 := by
    simpa [prefixWord, tailWord_8110347, baseEnd_8110347] using wordTrace_append hprefix tailTrace_8110347
  have hstable : (prefixWord ++ tailWord_8110347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110347).length < 2 ^ (prefixWord ++ tailWord_8110347).sum := by decide
  have hdescent : baseEnd_8110347 < baseStart_8110347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110375 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_8110375 : Nat := 118140960795 + 8110375 * 2 ^ 59
def prefixEnd_8110375 : Nat := 4983230072969 + 3 ^ 40 * 8110375 * 2
def baseEnd_8110375 : Nat := 4164520663208810854213571

theorem tailTrace_8110375 : CollatzResearch.WordTrace tailWord_8110375 prefixEnd_8110375 4164520663208810854213571 := by
  unfold tailWord_8110375
  simp only [CollatzResearch.WordTrace]
  refine ⟨295809677992503991618340579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197206451995002661078893719 295809677992503991618340579)
  ·
    refine ⟨443714516988755987427510869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295809677992503991618340579 443714516988755987427510869)
    ·
      refine ⟨5199779495961984227666143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 443714516988755987427510869 5199779495961984227666143)
      ·
        refine ⟨7799669243942976341499215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199779495961984227666143 7799669243942976341499215)
        ·
          refine ⟨11699503865914464512248823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799669243942976341499215 11699503865914464512248823)
          ·
            refine ⟨17549255798871696768373235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11699503865914464512248823 17549255798871696768373235)
            ·
              refine ⟨26323883698307545152559853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17549255798871696768373235 26323883698307545152559853)
              ·
                refine ⟨9871456386865329432209945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26323883698307545152559853 9871456386865329432209945)
                ·
                  refine ⟨7403592290148997074157459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871456386865329432209945 7403592290148997074157459)
                  ·
                    refine ⟨11105388435223495611236189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403592290148997074157459 11105388435223495611236189)
                    ·
                      refine ⟨4164520663208810854213571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11105388435223495611236189 4164520663208810854213571)
                      ·
                        rfl

theorem cell23_8110375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_8110375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110375 prefixEnd_8110375 := by exact prefixLift 8110375
  have htrace : WordTrace (prefixWord ++ tailWord_8110375) baseStart_8110375 baseEnd_8110375 := by
    simpa [prefixWord, tailWord_8110375, baseEnd_8110375] using wordTrace_append hprefix tailTrace_8110375
  have hstable : (prefixWord ++ tailWord_8110375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110375).length < 2 ^ (prefixWord ++ tailWord_8110375).sum := by decide
  have hdescent : baseEnd_8110375 < baseStart_8110375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110417 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_8110417 : Nat := 118140960795 + 8110417 * 2 ^ 59
def prefixEnd_8110417 : Nat := 4983230072969 + 3 ^ 40 * 8110417 * 2
def baseEnd_8110417 : Nat := 1388180743132099896629459

theorem tailTrace_8110417 : CollatzResearch.WordTrace tailWord_8110417 prefixEnd_8110417 1388180743132099896629459 := by
  unfold tailWord_8110417
  simp only [CollatzResearch.WordTrace]
  refine ⟨295811209858351832791369505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197207473238901221860913003 295811209858351832791369505)
  ·
    refine ⟨221858407393763874593527129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295811209858351832791369505 221858407393763874593527129)
    ·
      refine ⟨166393805545322905945145347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221858407393763874593527129 166393805545322905945145347)
      ·
        refine ⟨249590708317984358917718021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166393805545322905945145347 249590708317984358917718021)
        ·
          refine ⟨46798257809622067297072129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249590708317984358917718021 46798257809622067297072129)
          ·
            refine ⟨35098693357216550472804097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46798257809622067297072129 35098693357216550472804097)
            ·
              refine ⟨26324020017912412854603073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35098693357216550472804097 26324020017912412854603073)
              ·
                refine ⟨19743015013434309640952305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26324020017912412854603073 19743015013434309640952305)
                ·
                  refine ⟨14807261260075732230714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19743015013434309640952305 14807261260075732230714229)
                  ·
                    refine ⟨1388180743132099896629459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14807261260075732230714229 1388180743132099896629459)
                    ·
                      rfl

theorem cell23_8110417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_8110417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110417 prefixEnd_8110417 := by exact prefixLift 8110417
  have htrace : WordTrace (prefixWord ++ tailWord_8110417) baseStart_8110417 baseEnd_8110417 := by
    simpa [prefixWord, tailWord_8110417, baseEnd_8110417] using wordTrace_append hprefix tailTrace_8110417
  have hstable : (prefixWord ++ tailWord_8110417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110417).length < 2 ^ (prefixWord ++ tailWord_8110417).sum := by decide
  have hdescent : baseEnd_8110417 < baseStart_8110417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110514 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_8110514 : Nat := 118140960795 + 8110514 * 2 ^ 59
def prefixEnd_8110514 : Nat := 4983230072969 + 3 ^ 40 * 8110514 * 2
def baseEnd_8110514 : Nat := 4164592037019785810375431

theorem tailTrace_8110514 : CollatzResearch.WordTrace tailWord_8110514 prefixEnd_8110514 4164592037019785810375431 := by
  unfold tailWord_8110514
  simp only [CollatzResearch.WordTrace]
  refine ⟨73953686934750104589412649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197209831826000278905100397 73953686934750104589412649)
  ·
    refine ⟨55465265201062578442059487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73953686934750104589412649 55465265201062578442059487)
    ·
      refine ⟨83197897801593867663089231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55465265201062578442059487 83197897801593867663089231)
      ·
        refine ⟨124796846702390801494633847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83197897801593867663089231 124796846702390801494633847)
        ·
          refine ⟨187195270053586202241950771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124796846702390801494633847 187195270053586202241950771)
          ·
            refine ⟨280792905080379303362926157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187195270053586202241950771 280792905080379303362926157)
            ·
              refine ⟨105297339405142238761097309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280792905080379303362926157 105297339405142238761097309)
              ·
                refine ⟨39486502276928339535411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105297339405142238761097309 39486502276928339535411491)
                ·
                  refine ⟨59229753415392509303117237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39486502276928339535411491 59229753415392509303117237)
                  ·
                    refine ⟨5552789382693047747167241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59229753415392509303117237 5552789382693047747167241)
                    ·
                      refine ⟨4164592037019785810375431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552789382693047747167241 4164592037019785810375431)
                      ·
                        rfl

theorem cell23_8110514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_8110514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110514 prefixEnd_8110514 := by exact prefixLift 8110514
  have htrace : WordTrace (prefixWord ++ tailWord_8110514) baseStart_8110514 baseEnd_8110514 := by
    simpa [prefixWord, tailWord_8110514, baseEnd_8110514] using wordTrace_append hprefix tailTrace_8110514
  have hstable : (prefixWord ++ tailWord_8110514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110514).length < 2 ^ (prefixWord ++ tailWord_8110514).sum := by decide
  have hdescent : baseEnd_8110514 < baseStart_8110514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110527 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_8110527 : Nat := 118140960795 + 8110527 * 2 ^ 59
def prefixEnd_8110527 : Nat := 4983230072969 + 3 ^ 40 * 8110527 * 2
def baseEnd_8110527 : Nat := 4164598712268294259512871

theorem tailTrace_8110527 : CollatzResearch.WordTrace tailWord_8110527 prefixEnd_8110527 4164598712268294259512871 := by
  unfold tailWord_8110527
  simp only [CollatzResearch.WordTrace]
  refine ⟨295815221887953321577873835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197210147925302214385249223 295815221887953321577873835)
  ·
    refine ⟨443722832831929982366810753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295815221887953321577873835 443722832831929982366810753)
    ·
      refine ⟨332792124623947486775108065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443722832831929982366810753 332792124623947486775108065)
      ·
        refine ⟨249594093467960615081331049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332792124623947486775108065 249594093467960615081331049)
        ·
          refine ⟨187195570100970461310998287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249594093467960615081331049 187195570100970461310998287)
          ·
            refine ⟨280793355151455691966497431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187195570100970461310998287 280793355151455691966497431)
            ·
              refine ⟨421190032727183537949746147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280793355151455691966497431 421190032727183537949746147)
              ·
                refine ⟨631785049090775306924619221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421190032727183537949746147 631785049090775306924619221)
                ·
                  refine ⟨14807462088065046256045763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 631785049090775306924619221 14807462088065046256045763)
                  ·
                    refine ⟨22211193132097569384068645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14807462088065046256045763 22211193132097569384068645)
                    ·
                      refine ⟨4164598712268294259512871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22211193132097569384068645 4164598712268294259512871)
                      ·
                        rfl

theorem cell23_8110527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_8110527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110527 prefixEnd_8110527 := by exact prefixLift 8110527
  have htrace : WordTrace (prefixWord ++ tailWord_8110527) baseStart_8110527 baseEnd_8110527 := by
    simpa [prefixWord, tailWord_8110527, baseEnd_8110527] using wordTrace_append hprefix tailTrace_8110527
  have hstable : (prefixWord ++ tailWord_8110527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110527).length < 2 ^ (prefixWord ++ tailWord_8110527).sum := by decide
  have hdescent : baseEnd_8110527 < baseStart_8110527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110561 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_8110561 : Nat := 118140960795 + 8110561 * 2 ^ 59
def prefixEnd_8110561 : Nat := 4983230072969 + 3 ^ 40 * 8110561 * 2
def baseEnd_8110561 : Nat := 4164616170610547126487715

theorem tailTrace_8110561 : CollatzResearch.WordTrace tailWord_8110561 prefixEnd_8110561 4164616170610547126487715 := by
  unfold tailWord_8110561
  simp only [CollatzResearch.WordTrace]
  refine ⟨295816461969830145384611537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197210974646553430256407691 295816461969830145384611537)
  ·
    refine ⟨221862346477372609038458653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295816461969830145384611537 221862346477372609038458653)
    ·
      refine ⟨83198379929014728389421995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221862346477372609038458653 83198379929014728389421995)
      ·
        refine ⟨124797569893522092584132993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83198379929014728389421995 124797569893522092584132993)
        ·
          refine ⟨93598177420141569438099745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124797569893522092584132993 93598177420141569438099745)
          ·
            refine ⟨70198633065106177078574809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93598177420141569438099745 70198633065106177078574809)
            ·
              refine ⟨52648974798829632808931107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70198633065106177078574809 52648974798829632808931107)
              ·
                refine ⟨78973462198244449213396661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52648974798829632808931107 78973462198244449213396661)
                ·
                  refine ⟨7403762081085417113755937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78973462198244449213396661 7403762081085417113755937)
                  ·
                    refine ⟨5552821560814062835316953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403762081085417113755937 5552821560814062835316953)
                    ·
                      refine ⟨4164616170610547126487715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552821560814062835316953 4164616170610547126487715)
                      ·
                        rfl

theorem cell23_8110561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_8110561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110561 prefixEnd_8110561 := by exact prefixLift 8110561
  have htrace : WordTrace (prefixWord ++ tailWord_8110561) baseStart_8110561 baseEnd_8110561 := by
    simpa [prefixWord, tailWord_8110561, baseEnd_8110561] using wordTrace_append hprefix tailTrace_8110561
  have hstable : (prefixWord ++ tailWord_8110561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110561).length < 2 ^ (prefixWord ++ tailWord_8110561).sum := by decide
  have hdescent : baseEnd_8110561 < baseStart_8110561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110567 : List Nat := [1, 1, 5, 2, 1, 1, 1, 11]
def baseStart_8110567 : Nat := 118140960795 + 8110567 * 2 ^ 59
def prefixEnd_8110567 : Nat := 4983230072969 + 3 ^ 40 * 8110567 * 2
def baseEnd_8110567 : Nat := 154245157462758300111581

theorem tailTrace_8110567 : CollatzResearch.WordTrace tailWord_8110567 prefixEnd_8110567 154245157462758300111581 := by
  unfold tailWord_8110567
  simp only [CollatzResearch.WordTrace]
  refine ⟨295816680807808408409329955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197211120538538938939553303 295816680807808408409329955)
  ·
    refine ⟨443725021211712612613994933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295816680807808408409329955 443725021211712612613994933)
    ·
      refine ⟨41599220738598057432562025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443725021211712612613994933 41599220738598057432562025)
      ·
        refine ⟨31199415553948543074421519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41599220738598057432562025 31199415553948543074421519)
        ·
          refine ⟨46799123330922814611632279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31199415553948543074421519 46799123330922814611632279)
          ·
            refine ⟨70198684996384221917448419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46799123330922814611632279 70198684996384221917448419)
            ·
              refine ⟨105298027494576332876172629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70198684996384221917448419 105298027494576332876172629)
              ·
                refine ⟨154245157462758300111581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105298027494576332876172629 154245157462758300111581)
                ·
                  rfl

theorem cell23_8110567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 11].length) (baseStart_8110567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110567 prefixEnd_8110567 := by exact prefixLift 8110567
  have htrace : WordTrace (prefixWord ++ tailWord_8110567) baseStart_8110567 baseEnd_8110567 := by
    simpa [prefixWord, tailWord_8110567, baseEnd_8110567] using wordTrace_append hprefix tailTrace_8110567
  have hstable : (prefixWord ++ tailWord_8110567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110567).length < 2 ^ (prefixWord ++ tailWord_8110567).sum := by decide
  have hdescent : baseEnd_8110567 < baseStart_8110567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110574 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_8110574 : Nat := 118140960795 + 8110574 * 2 ^ 59
def prefixEnd_8110574 : Nat := 4983230072969 + 3 ^ 40 * 8110574 * 2
def baseEnd_8110574 : Nat := 4164622845859055575625155

theorem tailTrace_8110574 : CollatzResearch.WordTrace tailWord_8110574 prefixEnd_8110574 4164622845859055575625155 := by
  unfold tailWord_8110574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36977117014847881075604347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197211290745855365736556517 36977117014847881075604347)
  ·
    refine ⟨55465675522271821613406521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36977117014847881075604347 55465675522271821613406521)
    ·
      refine ⟨41599256641703866210054891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55465675522271821613406521 41599256641703866210054891)
      ·
        refine ⟨62398884962555799315082337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41599256641703866210054891 62398884962555799315082337)
        ·
          refine ⟨46799163721916849486311753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62398884962555799315082337 46799163721916849486311753)
          ·
            refine ⟨35099372791437637114733815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46799163721916849486311753 35099372791437637114733815)
            ·
              refine ⟨52649059187156455672100723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35099372791437637114733815 52649059187156455672100723)
              ·
                refine ⟨78973588780734683508151085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52649059187156455672100723 78973588780734683508151085)
                ·
                  refine ⟨29615095792775506315556657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78973588780734683508151085 29615095792775506315556657)
                  ·
                    refine ⟨22211321844581629736667493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29615095792775506315556657 22211321844581629736667493)
                    ·
                      refine ⟨4164622845859055575625155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22211321844581629736667493 4164622845859055575625155)
                      ·
                        rfl

theorem cell23_8110574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_8110574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110574 prefixEnd_8110574 := by exact prefixLift 8110574
  have htrace : WordTrace (prefixWord ++ tailWord_8110574) baseStart_8110574 baseEnd_8110574 := by
    simpa [prefixWord, tailWord_8110574, baseEnd_8110574] using wordTrace_append hprefix tailTrace_8110574
  have hstable : (prefixWord ++ tailWord_8110574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110574).length < 2 ^ (prefixWord ++ tailWord_8110574).sum := by decide
  have hdescent : baseEnd_8110574 < baseStart_8110574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110597 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_8110597 : Nat := 118140960795 + 8110597 * 2 ^ 59
def prefixEnd_8110597 : Nat := 4983230072969 + 3 ^ 40 * 8110597 * 2
def baseEnd_8110597 : Nat := 1388211551971369661879183

theorem tailTrace_8110597 : CollatzResearch.WordTrace tailWord_8110597 prefixEnd_8110597 1388211551971369661879183 := by
  unfold tailWord_8110597
  simp only [CollatzResearch.WordTrace]
  refine ⟨295817774997699723532922045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197211849998466482355281363 295817774997699723532922045)
  ·
    refine ⟨110931665624137396324845767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295817774997699723532922045 110931665624137396324845767)
    ·
      refine ⟨166397498436206094487268651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110931665624137396324845767 166397498436206094487268651)
      ·
        refine ⟨249596247654309141730902977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166397498436206094487268651 249596247654309141730902977)
        ·
          refine ⟨187197185740731856298177233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249596247654309141730902977 187197185740731856298177233)
          ·
            refine ⟨140397889305548892223632925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187197185740731856298177233 140397889305548892223632925)
            ·
              refine ⟨52649208489580834583862347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140397889305548892223632925 52649208489580834583862347)
              ·
                refine ⟨78973812734371251875793521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52649208489580834583862347 78973812734371251875793521)
                ·
                  refine ⟨59230359550778438906845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78973812734371251875793521 59230359550778438906845141)
                  ·
                    refine ⟨1388211551971369661879183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59230359550778438906845141 1388211551971369661879183)
                    ·
                      rfl

theorem cell23_8110597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_8110597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110597 prefixEnd_8110597 := by exact prefixLift 8110597
  have htrace : WordTrace (prefixWord ++ tailWord_8110597) baseStart_8110597 baseEnd_8110597 := by
    simpa [prefixWord, tailWord_8110597, baseEnd_8110597] using wordTrace_append hprefix tailTrace_8110597
  have hstable : (prefixWord ++ tailWord_8110597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110597).length < 2 ^ (prefixWord ++ tailWord_8110597).sum := by decide
  have hdescent : baseEnd_8110597 < baseStart_8110597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110605 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_8110605 : Nat := 118140960795 + 8110605 * 2 ^ 59
def prefixEnd_8110605 : Nat := 4983230072969 + 3 ^ 40 * 8110605 * 2
def baseEnd_8110605 : Nat := 1388212921253114984779171

theorem tailTrace_8110605 : CollatzResearch.WordTrace tailWord_8110605 prefixEnd_8110605 1388212921253114984779171 := by
  unfold tailWord_8110605
  simp only [CollatzResearch.WordTrace]
  refine ⟨295818066781670740899213269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197212044521113827266142179 295818066781670740899213269)
  ·
    refine ⟨6933235940195407989825311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 295818066781670740899213269 6933235940195407989825311)
    ·
      refine ⟨10399853910293111984737967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6933235940195407989825311 10399853910293111984737967)
      ·
        refine ⟨15599780865439667977106951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10399853910293111984737967 15599780865439667977106951)
        ·
          refine ⟨23399671298159501965660427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15599780865439667977106951 23399671298159501965660427)
          ·
            refine ⟨35099506947239252948490641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23399671298159501965660427 35099506947239252948490641)
            ·
              refine ⟨26324630210429439711367981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35099506947239252948490641 26324630210429439711367981)
              ·
                refine ⟨9871736328911039891762993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26324630210429439711367981 9871736328911039891762993)
                ·
                  refine ⟨7403802246683279918822245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871736328911039891762993 7403802246683279918822245)
                  ·
                    refine ⟨1388212921253114984779171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403802246683279918822245 1388212921253114984779171)
                    ·
                      rfl

theorem cell23_8110605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_8110605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110605 prefixEnd_8110605 := by exact prefixLift 8110605
  have htrace : WordTrace (prefixWord ++ tailWord_8110605) baseStart_8110605 baseEnd_8110605 := by
    simpa [prefixWord, tailWord_8110605, baseEnd_8110605] using wordTrace_append hprefix tailTrace_8110605
  have hstable : (prefixWord ++ tailWord_8110605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110605).length < 2 ^ (prefixWord ++ tailWord_8110605).sum := by decide
  have hdescent : baseEnd_8110605 < baseStart_8110605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110611 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 3]
def baseStart_8110611 : Nat := 118140960795 + 8110611 * 2 ^ 59
def prefixEnd_8110611 : Nat := 4983230072969 + 3 ^ 40 * 8110611 * 2
def baseEnd_8110611 : Nat := 4164641844643271930862485

theorem tailTrace_8110611 : CollatzResearch.WordTrace tailWord_8110611 prefixEnd_8110611 4164641844643271930862485 := by
  unfold tailWord_8110611
  simp only [CollatzResearch.WordTrace]
  refine ⟨295818285619649003923931687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197212190413099335949287791 295818285619649003923931687)
  ·
    refine ⟨443727428429473505885897531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295818285619649003923931687 443727428429473505885897531)
    ·
      refine ⟨665591142644210258828846297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443727428429473505885897531 665591142644210258828846297)
      ·
        refine ⟨499193356983157694121634723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665591142644210258828846297 499193356983157694121634723)
        ·
          refine ⟨748790035474736541182452085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499193356983157694121634723 748790035474736541182452085)
          ·
            refine ⟨70199065825756550735854883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 748790035474736541182452085 70199065825756550735854883)
            ·
              refine ⟨105298598738634826103782325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70199065825756550735854883 105298598738634826103782325)
              ·
                refine ⟨9871743631747014947229593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105298598738634826103782325 9871743631747014947229593)
                ·
                  refine ⟨7403807723810261210422195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9871743631747014947229593 7403807723810261210422195)
                  ·
                    refine ⟨11105711585715391815633293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7403807723810261210422195 11105711585715391815633293)
                    ·
                      refine ⟨4164641844643271930862485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11105711585715391815633293 4164641844643271930862485)
                      ·
                        rfl

theorem cell23_8110611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_8110611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110611 prefixEnd_8110611 := by exact prefixLift 8110611
  have htrace : WordTrace (prefixWord ++ tailWord_8110611) baseStart_8110611 baseEnd_8110611 := by
    simpa [prefixWord, tailWord_8110611, baseEnd_8110611] using wordTrace_append hprefix tailTrace_8110611
  have hstable : (prefixWord ++ tailWord_8110611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110611).length < 2 ^ (prefixWord ++ tailWord_8110611).sum := by decide
  have hdescent : baseEnd_8110611 < baseStart_8110611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110674 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_8110674 : Nat := 118140960795 + 8110674 * 2 ^ 59
def prefixEnd_8110674 : Nat := 4983230072969 + 3 ^ 40 * 8110674 * 2
def baseEnd_8110674 : Nat := 462741577102722798263855

theorem tailTrace_8110674 : CollatzResearch.WordTrace tailWord_8110674 prefixEnd_8110674 462741577102722798263855 := by
  unfold tailWord_8110674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73955145854605191420868769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197213722278947177122316717 73955145854605191420868769)
  ·
    refine ⟨55466359390953893565651577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73955145854605191420868769 55466359390953893565651577)
    ·
      refine ⟨41599769543215420174238683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55466359390953893565651577 41599769543215420174238683)
      ·
        refine ⟨62399654314823130261358025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41599769543215420174238683 62399654314823130261358025)
        ·
          refine ⟨46799740736117347696018519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62399654314823130261358025 46799740736117347696018519)
          ·
            refine ⟨70199611104176021544027779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46799740736117347696018519 70199611104176021544027779)
            ·
              refine ⟨105299416656264032316041669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70199611104176021544027779 105299416656264032316041669)
              ·
                refine ⟨19743640623049506059257813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105299416656264032316041669 19743640623049506059257813)
                ·
                  refine ⟨462741577102722798263855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19743640623049506059257813 462741577102722798263855)
                  ·
                    rfl

theorem cell23_8110674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_8110674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110674 prefixEnd_8110674 := by exact prefixLift 8110674
  have htrace : WordTrace (prefixWord ++ tailWord_8110674) baseStart_8110674 baseEnd_8110674 := by
    simpa [prefixWord, tailWord_8110674, baseEnd_8110674] using wordTrace_append hprefix tailTrace_8110674
  have hstable : (prefixWord ++ tailWord_8110674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110674).length < 2 ^ (prefixWord ++ tailWord_8110674).sum := by decide
  have hdescent : baseEnd_8110674 < baseStart_8110674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110738 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_8110738 : Nat := 118140960795 + 8110738 * 2 ^ 59
def prefixEnd_8110738 : Nat := 4983230072969 + 3 ^ 40 * 8110738 * 2
def baseEnd_8110738 : Nat := 1388235685562130977991467

theorem tailTrace_8110738 : CollatzResearch.WordTrace tailWord_8110738 prefixEnd_8110738 1388235685562130977991467 := by
  unfold tailWord_8110738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73955729422547226153451217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197215278460125936409203245 73955729422547226153451217)
  ·
    refine ⟨55466797066910419615088413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73955729422547226153451217 55466797066910419615088413)
    ·
      refine ⟨20800048900091407355658155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55466797066910419615088413 20800048900091407355658155)
      ·
        refine ⟨31200073350137111033487233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20800048900091407355658155 31200073350137111033487233)
        ·
          refine ⟨23400055012602833275115425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31200073350137111033487233 23400055012602833275115425)
          ·
            refine ⟨17550041259452124956336569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23400055012602833275115425 17550041259452124956336569)
            ·
              refine ⟨13162530944589093717252427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550041259452124956336569 13162530944589093717252427)
              ·
                refine ⟨19743796416883640575878641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13162530944589093717252427 19743796416883640575878641)
                ·
                  refine ⟨14807847312662730431908981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19743796416883640575878641 14807847312662730431908981)
                  ·
                    refine ⟨1388235685562130977991467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14807847312662730431908981 1388235685562130977991467)
                    ·
                      rfl

theorem cell23_8110738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_8110738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110738 prefixEnd_8110738 := by exact prefixLift 8110738
  have htrace : WordTrace (prefixWord ++ tailWord_8110738) baseStart_8110738 baseEnd_8110738 := by
    simpa [prefixWord, tailWord_8110738, baseEnd_8110738] using wordTrace_append hprefix tailTrace_8110738
  have hstable : (prefixWord ++ tailWord_8110738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110738).length < 2 ^ (prefixWord ++ tailWord_8110738).sum := by decide
  have hdescent : baseEnd_8110738 < baseStart_8110738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110741 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_8110741 : Nat := 118140960795 + 8110741 * 2 ^ 59
def prefixEnd_8110741 : Nat := 4983230072969 + 3 ^ 40 * 8110741 * 2
def baseEnd_8110741 : Nat := 4164708597128356422236887

theorem tailTrace_8110741 : CollatzResearch.WordTrace tailWord_8110741 prefixEnd_8110741 4164708597128356422236887 := by
  unfold tailWord_8110741
  simp only [CollatzResearch.WordTrace]
  refine ⟨295823027109178036126164077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197215351406118690750776051 295823027109178036126164077)
  ·
    refine ⟨110933635165941763547311529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295823027109178036126164077 110933635165941763547311529)
    ·
      refine ⟨83200226374456322660483647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110933635165941763547311529 83200226374456322660483647)
      ·
        refine ⟨124800339561684483990725471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83200226374456322660483647 124800339561684483990725471)
        ·
          refine ⟨187200509342526725986088207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124800339561684483990725471 187200509342526725986088207)
          ·
            refine ⟨280800764013790088979132311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187200509342526725986088207 280800764013790088979132311)
            ·
              refine ⟨421201146020685133468698467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280800764013790088979132311 421201146020685133468698467)
              ·
                refine ⟨631801719031027700203047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421201146020685133468698467 631801719031027700203047701)
                ·
                  refine ⟨29615705579579423447017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 631801719031027700203047701 29615705579579423447017861)
                  ·
                    refine ⟨5552944796171141896315849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29615705579579423447017861 5552944796171141896315849)
                    ·
                      refine ⟨4164708597128356422236887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5552944796171141896315849 4164708597128356422236887)
                      ·
                        rfl

theorem cell23_8110741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_8110741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110741 prefixEnd_8110741 := by exact prefixLift 8110741
  have htrace : WordTrace (prefixWord ++ tailWord_8110741) baseStart_8110741 baseEnd_8110741 := by
    simpa [prefixWord, tailWord_8110741, baseEnd_8110741] using wordTrace_append hprefix tailTrace_8110741
  have hstable : (prefixWord ++ tailWord_8110741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110741).length < 2 ^ (prefixWord ++ tailWord_8110741).sum := by decide
  have hdescent : baseEnd_8110741 < baseStart_8110741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110759 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 5]
def baseStart_8110759 : Nat := 118140960795 + 8110759 * 2 ^ 59
def prefixEnd_8110759 : Nat := 4983230072969 + 3 ^ 40 * 8110759 * 2
def baseEnd_8110759 : Nat := 462746426642237483534645

theorem tailTrace_8110759 : CollatzResearch.WordTrace tailWord_8110759 prefixEnd_8110759 462746426642237483534645 := by
  unfold tailWord_8110759
  simp only [CollatzResearch.WordTrace]
  refine ⟨295823683623112825200319331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197215789082075216800212887 295823683623112825200319331)
  ·
    refine ⟨443735525434669237800478997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295823683623112825200319331 443735525434669237800478997)
    ·
      refine ⟨20800102754750120521897453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443735525434669237800478997 20800102754750120521897453)
      ·
        refine ⟨7800038533031295195711545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20800102754750120521897453 7800038533031295195711545)
        ·
          refine ⟨5850028899773471396783659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7800038533031295195711545 5850028899773471396783659)
          ·
            refine ⟨8775043349660207095175489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850028899773471396783659 8775043349660207095175489)
            ·
              refine ⟨6581282512245155321381617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775043349660207095175489 6581282512245155321381617)
              ·
                refine ⟨4935961884183866491036213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581282512245155321381617 4935961884183866491036213)
                ·
                  refine ⟨462746426642237483534645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935961884183866491036213 462746426642237483534645)
                  ·
                    rfl

theorem cell23_8110759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 5].length) (baseStart_8110759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110759 prefixEnd_8110759 := by exact prefixLift 8110759
  have htrace : WordTrace (prefixWord ++ tailWord_8110759) baseStart_8110759 baseEnd_8110759 := by
    simpa [prefixWord, tailWord_8110759, baseEnd_8110759] using wordTrace_append hprefix tailTrace_8110759
  have hstable : (prefixWord ++ tailWord_8110759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110759).length < 2 ^ (prefixWord ++ tailWord_8110759).sum := by decide
  have hdescent : baseEnd_8110759 < baseStart_8110759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110781 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 6]
def baseStart_8110781 : Nat := 118140960795 + 8110781 * 2 ^ 59
def prefixEnd_8110781 : Nat := 4983230072969 + 3 ^ 40 * 8110781 * 2
def baseEnd_8110781 : Nat := 462747681817170696192967

theorem tailTrace_8110781 : CollatzResearch.WordTrace tailWord_8110781 prefixEnd_8110781 462747681817170696192967 := by
  unfold tailWord_8110781
  simp only [CollatzResearch.WordTrace]
  refine ⟨295824486029033122957620197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197216324019355415305080131 295824486029033122957620197)
  ·
    refine ⟨55467091130443710554553787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295824486029033122957620197 55467091130443710554553787)
    ·
      refine ⟨83200636695665565831830681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55467091130443710554553787 83200636695665565831830681)
      ·
        refine ⟨62400477521749174373873011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83200636695665565831830681 62400477521749174373873011)
        ·
          refine ⟨93600716282623761560809517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62400477521749174373873011 93600716282623761560809517)
          ·
            refine ⟨35100268605983910585303569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93600716282623761560809517 35100268605983910585303569)
            ·
              refine ⟨26325201454487932938977677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35100268605983910585303569 26325201454487932938977677)
              ·
                refine ⟨9871950545432974852116629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26325201454487932938977677 9871950545432974852116629)
                ·
                  refine ⟨462747681817170696192967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9871950545432974852116629 462747681817170696192967)
                  ·
                    rfl

theorem cell23_8110781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_8110781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110781 prefixEnd_8110781 := by exact prefixLift 8110781
  have htrace : WordTrace (prefixWord ++ tailWord_8110781) baseStart_8110781 baseEnd_8110781 := by
    simpa [prefixWord, tailWord_8110781, baseEnd_8110781] using wordTrace_append hprefix tailTrace_8110781
  have hstable : (prefixWord ++ tailWord_8110781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110781).length < 2 ^ (prefixWord ++ tailWord_8110781).sum := by decide
  have hdescent : baseEnd_8110781 < baseStart_8110781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110802 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_8110802 : Nat := 118140960795 + 8110802 * 2 ^ 59
def prefixEnd_8110802 : Nat := 4983230072969 + 3 ^ 40 * 8110802 * 2
def baseEnd_8110802 : Nat := 1388246639816093561191369

theorem tailTrace_8110802 : CollatzResearch.WordTrace tailWord_8110802 prefixEnd_8110802 1388246639816093561191369 := by
  unfold tailWord_8110802
  simp only [CollatzResearch.WordTrace]
  refine ⟨73956312990489260886033665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197216834641304695696089773 73956312990489260886033665)
  ·
    refine ⟨55467234742866945664525249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73956312990489260886033665 55467234742866945664525249)
    ·
      refine ⟨41600426057150209248393937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55467234742866945664525249 41600426057150209248393937)
      ·
        refine ⟨31200319542862656936295453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41600426057150209248393937 31200319542862656936295453)
        ·
          refine ⟨11700119828573496351110795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31200319542862656936295453 11700119828573496351110795)
          ·
            refine ⟨17550179742860244526666193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700119828573496351110795 17550179742860244526666193)
            ·
              refine ⟨13162634807145183394999645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550179742860244526666193 13162634807145183394999645)
              ·
                refine ⟨4935988052679443773124867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13162634807145183394999645 4935988052679443773124867)
                ·
                  refine ⟨7403982079019165659687301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935988052679443773124867 7403982079019165659687301)
                  ·
                    refine ⟨1388246639816093561191369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403982079019165659687301 1388246639816093561191369)
                    ·
                      rfl

theorem cell23_8110802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_8110802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110802 prefixEnd_8110802 := by exact prefixLift 8110802
  have htrace : WordTrace (prefixWord ++ tailWord_8110802) baseStart_8110802 baseEnd_8110802 := by
    simpa [prefixWord, tailWord_8110802, baseEnd_8110802] using wordTrace_append hprefix tailTrace_8110802
  have hstable : (prefixWord ++ tailWord_8110802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110802).length < 2 ^ (prefixWord ++ tailWord_8110802).sum := by decide
  have hdescent : baseEnd_8110802 < baseStart_8110802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110825 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 1, 1, 3]
def baseStart_8110825 : Nat := 118140960795 + 8110825 * 2 ^ 59
def prefixEnd_8110825 : Nat := 4983230072969 + 3 ^ 40 * 8110825 * 2
def baseEnd_8110825 : Nat := 4164751729503334093586501

theorem tailTrace_8110825 : CollatzResearch.WordTrace tailWord_8110825 prefixEnd_8110825 4164751729503334093586501 := by
  unfold tailWord_8110825
  simp only [CollatzResearch.WordTrace]
  refine ⟨295826090840873718472221929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197217393893915812314814619 295826090840873718472221929)
  ·
    refine ⟨221869568130655288854166447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295826090840873718472221929 221869568130655288854166447)
    ·
      refine ⟨332804352195982933281249671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221869568130655288854166447 332804352195982933281249671)
      ·
        refine ⟨499206528293974399921874507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332804352195982933281249671 499206528293974399921874507)
        ·
          refine ⟨748809792440961599882811761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499206528293974399921874507 748809792440961599882811761)
          ·
            refine ⟨561607344330721199912108821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748809792440961599882811761 561607344330721199912108821)
            ·
              refine ⟨26325344265502556245880101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561607344330721199912108821 26325344265502556245880101)
              ·
                refine ⟨4936002049781729296102519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26325344265502556245880101 4936002049781729296102519)
                ·
                  refine ⟨7404003074672593944153779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936002049781729296102519 7404003074672593944153779)
                  ·
                    refine ⟨11106004612008890916230669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404003074672593944153779 11106004612008890916230669)
                    ·
                      refine ⟨4164751729503334093586501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106004612008890916230669 4164751729503334093586501)
                      ·
                        rfl

theorem cell23_8110825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 1, 1, 3].length) (baseStart_8110825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110825 prefixEnd_8110825 := by exact prefixLift 8110825
  have htrace : WordTrace (prefixWord ++ tailWord_8110825) baseStart_8110825 baseEnd_8110825 := by
    simpa [prefixWord, tailWord_8110825, baseEnd_8110825] using wordTrace_append hprefix tailTrace_8110825
  have hstable : (prefixWord ++ tailWord_8110825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110825).length < 2 ^ (prefixWord ++ tailWord_8110825).sum := by decide
  have hdescent : baseEnd_8110825 < baseStart_8110825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110882 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_8110882 : Nat := 118140960795 + 8110882 * 2 ^ 59
def prefixEnd_8110882 : Nat := 4983230072969 + 3 ^ 40 * 8110882 * 2
def baseEnd_8110882 : Nat := 4164780997900640370573739

theorem tailTrace_8110882 : CollatzResearch.WordTrace tailWord_8110882 prefixEnd_8110882 4164780997900640370573739 := by
  unfold tailWord_8110882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73957042450416804301761725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197218779867778144804697933 73957042450416804301761725)
  ·
    refine ⟨27733890918906301613160647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73957042450416804301761725 27733890918906301613160647)
    ·
      refine ⟨41600836378359452419740971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27733890918906301613160647 41600836378359452419740971)
      ·
        refine ⟨62401254567539178629611457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41600836378359452419740971 62401254567539178629611457)
        ·
          refine ⟨46800940925654383972208593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62401254567539178629611457 46800940925654383972208593)
          ·
            refine ⟨35100705694240787979156445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46800940925654383972208593 35100705694240787979156445)
            ·
              refine ⟨13162764635340295492183667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35100705694240787979156445 13162764635340295492183667)
              ·
                refine ⟨19744146953010443238275501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13162764635340295492183667 19744146953010443238275501)
                ·
                  refine ⟨7404055107378916214353313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19744146953010443238275501 7404055107378916214353313)
                  ·
                    refine ⟨5553041330534187160764985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7404055107378916214353313 5553041330534187160764985)
                    ·
                      refine ⟨4164780997900640370573739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553041330534187160764985 4164780997900640370573739)
                      ·
                        rfl

theorem cell23_8110882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_8110882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110882 prefixEnd_8110882 := by exact prefixLift 8110882
  have htrace : WordTrace (prefixWord ++ tailWord_8110882) baseStart_8110882 baseEnd_8110882 := by
    simpa [prefixWord, tailWord_8110882, baseEnd_8110882] using wordTrace_append hprefix tailTrace_8110882
  have hstable : (prefixWord ++ tailWord_8110882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110882).length < 2 ^ (prefixWord ++ tailWord_8110882).sum := by decide
  have hdescent : baseEnd_8110882 < baseStart_8110882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110898 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_8110898 : Nat := 118140960795 + 8110898 * 2 ^ 59
def prefixEnd_8110898 : Nat := 4983230072969 + 3 ^ 40 * 8110898 * 2
def baseEnd_8110898 : Nat := 4164789213591112307973665

theorem tailTrace_8110898 : CollatzResearch.WordTrace tailWord_8110898 prefixEnd_8110898 4164789213591112307973665 := by
  unfold tailWord_8110898
  simp only [CollatzResearch.WordTrace]
  refine ⟨73957188342402312984907337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197219168913072834626419565 73957188342402312984907337)
  ·
    refine ⟨55467891256801734738680503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73957188342402312984907337 55467891256801734738680503)
    ·
      refine ⟨83201836885202602108020755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55467891256801734738680503 83201836885202602108020755)
      ·
        refine ⟨124802755327803903162031133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83201836885202602108020755 124802755327803903162031133)
        ·
          refine ⟨46801033247926463685761675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124802755327803903162031133 46801033247926463685761675)
          ·
            refine ⟨70201549871889695528642513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46801033247926463685761675 70201549871889695528642513)
            ·
              refine ⟨52651162403917271646481885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70201549871889695528642513 52651162403917271646481885)
              ·
                refine ⟨19744185901468976867430707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52651162403917271646481885 19744185901468976867430707)
                ·
                  refine ⟨29616278852203465301146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19744185901468976867430707 29616278852203465301146061)
                  ·
                    refine ⟨11106104569576299487929773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29616278852203465301146061 11106104569576299487929773)
                    ·
                      refine ⟨4164789213591112307973665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106104569576299487929773 4164789213591112307973665)
                      ·
                        rfl

theorem cell23_8110898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_8110898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110898 prefixEnd_8110898 := by exact prefixLift 8110898
  have htrace : WordTrace (prefixWord ++ tailWord_8110898) baseStart_8110898 baseEnd_8110898 := by
    simpa [prefixWord, tailWord_8110898, baseEnd_8110898] using wordTrace_append hprefix tailTrace_8110898
  have hstable : (prefixWord ++ tailWord_8110898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110898).length < 2 ^ (prefixWord ++ tailWord_8110898).sum := by decide
  have hdescent : baseEnd_8110898 < baseStart_8110898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110902 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_8110902 : Nat := 118140960795 + 8110902 * 2 ^ 59
def prefixEnd_8110902 : Nat := 4983230072969 + 3 ^ 40 * 8110902 * 2
def baseEnd_8110902 : Nat := 4164791267513730292323647

theorem tailTrace_8110902 : CollatzResearch.WordTrace tailWord_8110902 prefixEnd_8110902 4164791267513730292323647 := by
  unfold tailWord_8110902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489306203849672538923435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197219266174396507081849973 18489306203849672538923435)
  ·
    refine ⟨27733959305774508808385153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489306203849672538923435 27733959305774508808385153)
    ·
      refine ⟨20800469479330881606288865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27733959305774508808385153 20800469479330881606288865)
      ·
        refine ⟨15600352109498161204716649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20800469479330881606288865 15600352109498161204716649)
        ·
          refine ⟨11700264082123620903537487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15600352109498161204716649 11700264082123620903537487)
          ·
            refine ⟨17550396123185431355306231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700264082123620903537487 17550396123185431355306231)
            ·
              refine ⟨26325594184778147032959347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17550396123185431355306231 26325594184778147032959347)
              ·
                refine ⟨39488391277167220549439021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26325594184778147032959347 39488391277167220549439021)
                ·
                  refine ⟨14808146728937707706039633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39488391277167220549439021 14808146728937707706039633)
                  ·
                    refine ⟨11106110046703280779529725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14808146728937707706039633 11106110046703280779529725)
                    ·
                      refine ⟨4164791267513730292323647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106110046703280779529725 4164791267513730292323647)
                      ·
                        rfl

theorem cell23_8110902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_8110902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110902 prefixEnd_8110902 := by exact prefixLift 8110902
  have htrace : WordTrace (prefixWord ++ tailWord_8110902) baseStart_8110902 baseEnd_8110902 := by
    simpa [prefixWord, tailWord_8110902, baseEnd_8110902] using wordTrace_append hprefix tailTrace_8110902
  have hstable : (prefixWord ++ tailWord_8110902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110902).length < 2 ^ (prefixWord ++ tailWord_8110902).sum := by decide
  have hdescent : baseEnd_8110902 < baseStart_8110902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110948 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_8110948 : Nat := 118140960795 + 8110948 * 2 ^ 59
def prefixEnd_8110948 : Nat := 4983230072969 + 3 ^ 40 * 8110948 * 2
def baseEnd_8110948 : Nat := 1388271629207945704116145

theorem tailTrace_8110948 : CollatzResearch.WordTrace tailWord_8110948 prefixEnd_8110948 1388271629207945704116145 := by
  unfold tailWord_8110948
  simp only [CollatzResearch.WordTrace]
  refine ⟨147915288509714055239474749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197220384679618740319299665 147915288509714055239474749)
  ·
    refine ⟨55468233191142770714803031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147915288509714055239474749 55468233191142770714803031)
    ·
      refine ⟨83202349786714156072204547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55468233191142770714803031 83202349786714156072204547)
      ·
        refine ⟨124803524680071234108306821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83202349786714156072204547 124803524680071234108306821)
        ·
          refine ⟨23400660877513356395307529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124803524680071234108306821 23400660877513356395307529)
          ·
            refine ⟨17550495658135017296480647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23400660877513356395307529 17550495658135017296480647)
            ·
              refine ⟨26325743487202525944720971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17550495658135017296480647 26325743487202525944720971)
              ·
                refine ⟨39488615230803788917081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26325743487202525944720971 39488615230803788917081457)
                ·
                  refine ⟨29616461423102841687811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39488615230803788917081457 29616461423102841687811093)
                  ·
                    refine ⟨1388271629207945704116145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29616461423102841687811093 1388271629207945704116145)
                    ·
                      rfl

theorem cell23_8110948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_8110948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110948 prefixEnd_8110948 := by exact prefixLift 8110948
  have htrace : WordTrace (prefixWord ++ tailWord_8110948) baseStart_8110948 baseEnd_8110948 := by
    simpa [prefixWord, tailWord_8110948, baseEnd_8110948] using wordTrace_append hprefix tailTrace_8110948
  have hstable : (prefixWord ++ tailWord_8110948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110948).length < 2 ^ (prefixWord ++ tailWord_8110948).sum := by decide
  have hdescent : baseEnd_8110948 < baseStart_8110948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110961 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 9]
def baseStart_8110961 : Nat := 118140960795 + 8110961 * 2 ^ 59
def prefixEnd_8110961 : Nat := 4983230072969 + 3 ^ 40 * 8110961 * 2
def baseEnd_8110961 : Nat := 462757951430260617942875

theorem tailTrace_8110961 : CollatzResearch.WordTrace tailWord_8110961 prefixEnd_8110961 462757951430260617942875 := by
  unfold tailWord_8110961
  simp only [CollatzResearch.WordTrace]
  refine ⟨295831051168381013699172737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197220700778920675799448491 295831051168381013699172737)
  ·
    refine ⟨221873288376285760274379553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295831051168381013699172737 221873288376285760274379553)
    ·
      refine ⟨166404966282214320205784665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221873288376285760274379553 166404966282214320205784665)
      ·
        refine ⟨124803724711660740154338499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166404966282214320205784665 124803724711660740154338499)
        ·
          refine ⟨187205587067491110231507749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124803724711660740154338499 187205587067491110231507749)
          ·
            refine ⟨35101047575154583168407703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187205587067491110231507749 35101047575154583168407703)
            ·
              refine ⟨52651571362731874752611555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35101047575154583168407703 52651571362731874752611555)
              ·
                refine ⟨78977357044097812128917333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52651571362731874752611555 78977357044097812128917333)
                ·
                  refine ⟨462757951430260617942875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78977357044097812128917333 462757951430260617942875)
                  ·
                    rfl

theorem cell23_8110961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_8110961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110961 prefixEnd_8110961 := by exact prefixLift 8110961
  have htrace : WordTrace (prefixWord ++ tailWord_8110961) baseStart_8110961 baseEnd_8110961 := by
    simpa [prefixWord, tailWord_8110961, baseEnd_8110961] using wordTrace_append hprefix tailTrace_8110961
  have hstable : (prefixWord ++ tailWord_8110961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110961).length < 2 ^ (prefixWord ++ tailWord_8110961).sum := by decide
  have hdescent : baseEnd_8110961 < baseStart_8110961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8110988 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_8110988 : Nat := 118140960795 + 8110988 * 2 ^ 59
def prefixEnd_8110988 : Nat := 4983230072969 + 3 ^ 40 * 8110988 * 2
def baseEnd_8110988 : Nat := 4164835426850016955848251

theorem tailTrace_8110988 : CollatzResearch.WordTrace tailWord_8110988 prefixEnd_8110988 4164835426850016955848251 := by
  unfold tailWord_8110988
  simp only [CollatzResearch.WordTrace]
  refine ⟨147916017969641598655202809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197221357292855464873603745 147916017969641598655202809)
  ·
    refine ⟨110937013477231198991402107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147916017969641598655202809 110937013477231198991402107)
    ·
      refine ⟨166405520215846798487103161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110937013477231198991402107 166405520215846798487103161)
      ·
        refine ⟨124804140161885098865327371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166405520215846798487103161 124804140161885098865327371)
        ·
          refine ⟨187206210242827648297991057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124804140161885098865327371 187206210242827648297991057)
          ·
            refine ⟨140404657682120736223493293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187206210242827648297991057 140404657682120736223493293)
            ·
              refine ⟨52651746630795276083809985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140404657682120736223493293 52651746630795276083809985)
              ·
                refine ⟨39488809973096457062857489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52651746630795276083809985 39488809973096457062857489)
                ·
                  refine ⟨29616607479822342797143117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39488809973096457062857489 29616607479822342797143117)
                  ·
                    refine ⟨11106227804933378548928669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29616607479822342797143117 11106227804933378548928669)
                    ·
                      refine ⟨4164835426850016955848251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106227804933378548928669 4164835426850016955848251)
                      ·
                        rfl

theorem cell23_8110988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_8110988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8110988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8110988 prefixEnd_8110988 := by exact prefixLift 8110988
  have htrace : WordTrace (prefixWord ++ tailWord_8110988) baseStart_8110988 baseEnd_8110988 := by
    simpa [prefixWord, tailWord_8110988, baseEnd_8110988] using wordTrace_append hprefix tailTrace_8110988
  have hstable : (prefixWord ++ tailWord_8110988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8110988).length < 2 ^ (prefixWord ++ tailWord_8110988).sum := by decide
  have hdescent : baseEnd_8110988 < baseStart_8110988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8110988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111001 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_8111001 : Nat := 118140960795 + 8111001 * 2 ^ 59
def prefixEnd_8111001 : Nat := 4983230072969 + 3 ^ 40 * 8111001 * 2
def baseEnd_8111001 : Nat := 4164842102098525404985691

theorem tailTrace_8111001 : CollatzResearch.WordTrace tailWord_8111001 prefixEnd_8111001 4164842102098525404985691 := by
  unfold tailWord_8111001
  simp only [CollatzResearch.WordTrace]
  refine ⟨295832510088236100530628857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197221673392157400353752571 295832510088236100530628857)
  ·
    refine ⟨221874382566177075397971643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295832510088236100530628857 221874382566177075397971643)
    ·
      refine ⟨332811573849265613096957465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221874382566177075397971643 332811573849265613096957465)
      ·
        refine ⟨249608680386949209822718099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332811573849265613096957465 249608680386949209822718099)
        ·
          refine ⟨374413020580423814734077149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249608680386949209822718099 374413020580423814734077149)
          ·
            refine ⟨140404882717658930525278931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374413020580423814734077149 140404882717658930525278931)
            ·
              refine ⟨210607324076488395787918397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140404882717658930525278931 210607324076488395787918397)
              ·
                refine ⟨78977746528683148420469399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210607324076488395787918397 78977746528683148420469399)
                ·
                  refine ⟨118466619793024722630704099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78977746528683148420469399 118466619793024722630704099)
                  ·
                    refine ⟨177699929689537083946056149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118466619793024722630704099 177699929689537083946056149)
                    ·
                      refine ⟨4164842102098525404985691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177699929689537083946056149 4164842102098525404985691)
                      ·
                        rfl

theorem cell23_8111001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_8111001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111001 prefixEnd_8111001 := by exact prefixLift 8111001
  have htrace : WordTrace (prefixWord ++ tailWord_8111001) baseStart_8111001 baseEnd_8111001 := by
    simpa [prefixWord, tailWord_8111001, baseEnd_8111001] using wordTrace_append hprefix tailTrace_8111001
  have hstable : (prefixWord ++ tailWord_8111001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111001).length < 2 ^ (prefixWord ++ tailWord_8111001).sum := by decide
  have hdescent : baseEnd_8111001 < baseStart_8111001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111055 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 3, 4]
def baseStart_8111055 : Nat := 118140960795 + 8111055 * 2 ^ 59
def prefixEnd_8111055 : Nat := 4983230072969 + 3 ^ 40 * 8111055 * 2
def baseEnd_8111055 : Nat := 1388289943351289397903481

theorem tailTrace_8111055 : CollatzResearch.WordTrace tailWord_8111055 prefixEnd_8111055 1388289943351289397903481 := by
  unfold tailWord_8111055
  simp only [CollatzResearch.WordTrace]
  refine ⟨295834479630040467753094619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197222986420026978502063079 295834479630040467753094619)
  ·
    refine ⟨443751719445060701629641929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295834479630040467753094619 443751719445060701629641929)
    ·
      refine ⟨332813789583795526222231447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443751719445060701629641929 332813789583795526222231447)
      ·
        refine ⟨499220684375693289333347171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332813789583795526222231447 499220684375693289333347171)
        ·
          refine ⟨748831026563539934000020757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499220684375693289333347171 748831026563539934000020757)
          ·
            refine ⟨35101454370165934406250973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 748831026563539934000020757 35101454370165934406250973)
            ·
              refine ⟨13163045388812225402344115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35101454370165934406250973 13163045388812225402344115)
              ·
                refine ⟨19744568083218338103516173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13163045388812225402344115 19744568083218338103516173)
                ·
                  refine ⟨7404213031206876788818565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19744568083218338103516173 7404213031206876788818565)
                  ·
                    refine ⟨1388289943351289397903481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7404213031206876788818565 1388289943351289397903481)
                    ·
                      rfl

theorem cell23_8111055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 4].length) (baseStart_8111055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111055 prefixEnd_8111055 := by exact prefixLift 8111055
  have htrace : WordTrace (prefixWord ++ tailWord_8111055) baseStart_8111055 baseEnd_8111055 := by
    simpa [prefixWord, tailWord_8111055, baseEnd_8111055] using wordTrace_append hprefix tailTrace_8111055
  have hstable : (prefixWord ++ tailWord_8111055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111055).length < 2 ^ (prefixWord ++ tailWord_8111055).sum := by decide
  have hdescent : baseEnd_8111055 < baseStart_8111055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111082 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_8111082 : Nat := 118140960795 + 8111082 * 2 ^ 59
def prefixEnd_8111082 : Nat := 4983230072969 + 3 ^ 40 * 8111082 * 2
def baseEnd_8111082 : Nat := 4164883694031539588072819

theorem tailTrace_8111082 : CollatzResearch.WordTrace tailWord_8111082 prefixEnd_8111082 4164883694031539588072819 := by
  unfold tailWord_8111082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73958866100235662841081875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197223642933961767576218333 73958866100235662841081875)
  ·
    refine ⟨110938299150353494261622813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73958866100235662841081875 110938299150353494261622813)
    ·
      refine ⟨41601862181382560348108555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110938299150353494261622813 41601862181382560348108555)
      ·
        refine ⟨62402793272073840522162833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41601862181382560348108555 62402793272073840522162833)
        ·
          refine ⟨46802094954055380391622125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62402793272073840522162833 46802094954055380391622125)
          ·
            refine ⟨17550785607770767646858297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46802094954055380391622125 17550785607770767646858297)
            ·
              refine ⟨13163089205828075735143723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17550785607770767646858297 13163089205828075735143723)
              ·
                refine ⟨19744633808742113602715585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13163089205828075735143723 19744633808742113602715585)
                ·
                  refine ⟨14808475356556585202036689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19744633808742113602715585 14808475356556585202036689)
                  ·
                    refine ⟨11106356517417438901527517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14808475356556585202036689 11106356517417438901527517)
                    ·
                      refine ⟨4164883694031539588072819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106356517417438901527517 4164883694031539588072819)
                      ·
                        rfl

theorem cell23_8111082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_8111082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111082 prefixEnd_8111082 := by exact prefixLift 8111082
  have htrace : WordTrace (prefixWord ++ tailWord_8111082) baseStart_8111082 baseEnd_8111082 := by
    simpa [prefixWord, tailWord_8111082, baseEnd_8111082] using wordTrace_append hprefix tailTrace_8111082
  have hstable : (prefixWord ++ tailWord_8111082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111082).length < 2 ^ (prefixWord ++ tailWord_8111082).sum := by decide
  have hdescent : baseEnd_8111082 < baseStart_8111082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111135 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_8111135 : Nat := 118140960795 + 8111135 * 2 ^ 59
def prefixEnd_8111135 : Nat := 4983230072969 + 3 ^ 40 * 8111135 * 2
def baseEnd_8111135 : Nat := 4164910908506227880710075

theorem tailTrace_8111135 : CollatzResearch.WordTrace tailWord_8111135 prefixEnd_8111135 4164910908506227880710075 := by
  unfold tailWord_8111135
  simp only [CollatzResearch.WordTrace]
  refine ⟨295837397469750641416006859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197224931646500427610671239 295837397469750641416006859)
  ·
    refine ⟨443756096204625962124010289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295837397469750641416006859 443756096204625962124010289)
    ·
      refine ⟨332817072153469471593007717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443756096204625962124010289 332817072153469471593007717)
      ·
        refine ⟨62403201028775525923688947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332817072153469471593007717 62403201028775525923688947)
        ·
          refine ⟨93604801543163288885533421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62403201028775525923688947 93604801543163288885533421)
          ·
            refine ⟨35101800578686233332075033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93604801543163288885533421 35101800578686233332075033)
            ·
              refine ⟨26326350434014674999056275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35101800578686233332075033 26326350434014674999056275)
              ·
                refine ⟨39489525651022012498584413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26326350434014674999056275 39489525651022012498584413)
                ·
                  refine ⟨14808572119133254686969155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39489525651022012498584413 14808572119133254686969155)
                  ·
                    refine ⟨22212858178699882030453733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14808572119133254686969155 22212858178699882030453733)
                    ·
                      refine ⟨4164910908506227880710075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22212858178699882030453733 4164910908506227880710075)
                      ·
                        rfl

theorem cell23_8111135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_8111135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111135 prefixEnd_8111135 := by exact prefixLift 8111135
  have htrace : WordTrace (prefixWord ++ tailWord_8111135) baseStart_8111135 baseEnd_8111135 := by
    simpa [prefixWord, tailWord_8111135, baseEnd_8111135] using wordTrace_append hprefix tailTrace_8111135
  have hstable : (prefixWord ++ tailWord_8111135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111135).length < 2 ^ (prefixWord ++ tailWord_8111135).sum := by decide
  have hdescent : baseEnd_8111135 < baseStart_8111135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111139 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 2, 3, 2]
def baseStart_8111139 : Nat := 118140960795 + 8111139 * 2 ^ 59
def prefixEnd_8111139 : Nat := 4983230072969 + 3 ^ 40 * 8111139 * 2
def baseEnd_8111139 : Nat := 4164912962428845865060057

theorem tailTrace_8111139 : CollatzResearch.WordTrace tailWord_8111139 prefixEnd_8111139 4164912962428845865060057 := by
  unfold tailWord_8111139
  simp only [CollatzResearch.WordTrace]
  refine ⟨295837543361736150099152471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197225028907824100066101647 295837543361736150099152471)
  ·
    refine ⟨443756315042604225148728707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295837543361736150099152471 443756315042604225148728707)
    ·
      refine ⟨665634472563906337723093061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443756315042604225148728707 665634472563906337723093061)
      ·
        refine ⟨124806463605732438323079949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665634472563906337723093061 124806463605732438323079949)
        ·
          refine ⟨46802423852149664371154981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124806463605732438323079949 46802423852149664371154981)
          ·
            refine ⟨8775454472278062069591559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46802423852149664371154981 8775454472278062069591559)
            ·
              refine ⟨13163181708417093104387339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8775454472278062069591559 13163181708417093104387339)
              ·
                refine ⟨19744772562625639656581009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13163181708417093104387339 19744772562625639656581009)
                ·
                  refine ⟨14808579421969229742435757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19744772562625639656581009 14808579421969229742435757)
                  ·
                    refine ⟨5553217283238461153413409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14808579421969229742435757 5553217283238461153413409)
                    ·
                      refine ⟨4164912962428845865060057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553217283238461153413409 4164912962428845865060057)
                      ·
                        rfl

theorem cell23_8111139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_8111139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111139 prefixEnd_8111139 := by exact prefixLift 8111139
  have htrace : WordTrace (prefixWord ++ tailWord_8111139) baseStart_8111139 baseEnd_8111139 := by
    simpa [prefixWord, tailWord_8111139, baseEnd_8111139] using wordTrace_append hprefix tailTrace_8111139
  have hstable : (prefixWord ++ tailWord_8111139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111139).length < 2 ^ (prefixWord ++ tailWord_8111139).sum := by decide
  have hdescent : baseEnd_8111139 < baseStart_8111139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111152 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2]
def baseStart_8111152 : Nat := 118140960795 + 8111152 * 2 ^ 59
def prefixEnd_8111152 : Nat := 4983230072969 + 3 ^ 40 * 8111152 * 2
def baseEnd_8111152 : Nat := 4164919637677354314197497

theorem tailTrace_8111152 : CollatzResearch.WordTrace tailWord_8111152 prefixEnd_8111152 4164919637677354314197497 := by
  unfold tailWord_8111152
  simp only [CollatzResearch.WordTrace]
  refine ⟨147919008755344526659687855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197225345007126035546250473 147919008755344526659687855)
  ·
    refine ⟨221878513133016789989531783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147919008755344526659687855 221878513133016789989531783)
    ·
      refine ⟨332817769699525184984297675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221878513133016789989531783 332817769699525184984297675)
      ·
        refine ⟨499226654549287777476446513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332817769699525184984297675 499226654549287777476446513)
        ·
          refine ⟨374419990911965833107334885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499226654549287777476446513 374419990911965833107334885)
          ·
            refine ⟨70203748295993593707625291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374419990911965833107334885 70203748295993593707625291)
            ·
              refine ⟨105305622443990390561437937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70203748295993593707625291 105305622443990390561437937)
              ·
                refine ⟨78979216832992792921078453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105305622443990390561437937 78979216832992792921078453)
                ·
                  refine ⟨7404301578093074336351105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78979216832992792921078453 7404301578093074336351105)
                  ·
                    refine ⟨5553226183569805752263329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7404301578093074336351105 5553226183569805752263329)
                    ·
                      refine ⟨4164919637677354314197497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553226183569805752263329 4164919637677354314197497)
                      ·
                        rfl

theorem cell23_8111152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 5, 2, 2].length) (baseStart_8111152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111152 prefixEnd_8111152 := by exact prefixLift 8111152
  have htrace : WordTrace (prefixWord ++ tailWord_8111152) baseStart_8111152 baseEnd_8111152 := by
    simpa [prefixWord, tailWord_8111152, baseEnd_8111152] using wordTrace_append hprefix tailTrace_8111152
  have hstable : (prefixWord ++ tailWord_8111152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111152).length < 2 ^ (prefixWord ++ tailWord_8111152).sum := by decide
  have hdescent : baseEnd_8111152 < baseStart_8111152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111162 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_8111162 : Nat := 118140960795 + 8111162 * 2 ^ 59
def prefixEnd_8111162 : Nat := 4983230072969 + 3 ^ 40 * 8111162 * 2
def baseEnd_8111162 : Nat := 1388308257494633091690817

theorem tailTrace_8111162 : CollatzResearch.WordTrace tailWord_8111162 prefixEnd_8111162 1388308257494633091690817 := by
  unfold tailWord_8111162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73959595560163206256809935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197225588160435216684826493 73959595560163206256809935)
  ·
    refine ⟨110939393340244809385214903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73959595560163206256809935 110939393340244809385214903)
    ·
      refine ⟨166409090010367214077822355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110939393340244809385214903 166409090010367214077822355)
      ·
        refine ⟨249613635015550821116733533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166409090010367214077822355 249613635015550821116733533)
        ·
          refine ⟨93605113130831557918775075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249613635015550821116733533 93605113130831557918775075)
          ·
            refine ⟨140407669696247336878162613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93605113130831557918775075 140407669696247336878162613)
            ·
              refine ⟨13163219034023187832327745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140407669696247336878162613 13163219034023187832327745)
              ·
                refine ⟨9872414275517390874245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13163219034023187832327745 9872414275517390874245809)
                ·
                  refine ⟨7404310706638043155684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872414275517390874245809 7404310706638043155684357)
                  ·
                    refine ⟨1388308257494633091690817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7404310706638043155684357 1388308257494633091690817)
                    ·
                      rfl

theorem cell23_8111162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_8111162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111162 prefixEnd_8111162 := by exact prefixLift 8111162
  have htrace : WordTrace (prefixWord ++ tailWord_8111162) baseStart_8111162 baseEnd_8111162 := by
    simpa [prefixWord, tailWord_8111162, baseEnd_8111162] using wordTrace_append hprefix tailTrace_8111162
  have hstable : (prefixWord ++ tailWord_8111162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111162).length < 2 ^ (prefixWord ++ tailWord_8111162).sum := by decide
  have hdescent : baseEnd_8111162 < baseStart_8111162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111236 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_8111236 : Nat := 118140960795 + 8111236 * 2 ^ 59
def prefixEnd_8111236 : Nat := 4983230072969 + 3 ^ 40 * 8111236 * 2
def baseEnd_8111236 : Nat := 4164962770052331985547111

theorem tailTrace_8111236 : CollatzResearch.WordTrace tailWord_8111236 prefixEnd_8111236 4164962770052331985547111 := by
  unfold tailWord_8111236
  simp only [CollatzResearch.WordTrace]
  refine ⟨147920540621192367832716781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197227387494923157110289041 147920540621192367832716781)
  ·
    refine ⟨55470202732947137937268793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147920540621192367832716781 55470202732947137937268793)
    ·
      refine ⟨41602652049710353452951595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55470202732947137937268793 41602652049710353452951595)
      ·
        refine ⟨62403978074565530179427393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41602652049710353452951595 62403978074565530179427393)
        ·
          refine ⟨46802983555924147634570545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62403978074565530179427393 46802983555924147634570545)
          ·
            refine ⟨35102237666943110725927909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46802983555924147634570545 35102237666943110725927909)
            ·
              refine ⟨6581669562551833261111483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35102237666943110725927909 6581669562551833261111483)
              ·
                refine ⟨9872504343827749891667225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581669562551833261111483 9872504343827749891667225)
                ·
                  refine ⟨7404378257870812418750419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872504343827749891667225 7404378257870812418750419)
                  ·
                    refine ⟨11106567386806218628125629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404378257870812418750419 11106567386806218628125629)
                    ·
                      refine ⟨4164962770052331985547111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106567386806218628125629 4164962770052331985547111)
                      ·
                        rfl

theorem cell23_8111236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_8111236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111236 prefixEnd_8111236 := by exact prefixLift 8111236
  have htrace : WordTrace (prefixWord ++ tailWord_8111236) baseStart_8111236 baseEnd_8111236 := by
    simpa [prefixWord, tailWord_8111236, baseEnd_8111236] using wordTrace_append hprefix tailTrace_8111236
  have hstable : (prefixWord ++ tailWord_8111236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111236).length < 2 ^ (prefixWord ++ tailWord_8111236).sum := by decide
  have hdescent : baseEnd_8111236 < baseStart_8111236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111246 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_8111246 : Nat := 118140960795 + 8111246 * 2 ^ 59
def prefixEnd_8111246 : Nat := 4983230072969 + 3 ^ 40 * 8111246 * 2
def baseEnd_8111246 : Nat := 4164967904858876946422065

theorem tailTrace_8111246 : CollatzResearch.WordTrace tailWord_8111246 prefixEnd_8111246 4164967904858876946422065 := by
  unfold tailWord_8111246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980180746543563421662199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197227630648232338248865061 36980180746543563421662199)
  ·
    refine ⟨55470271119815345132493299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36980180746543563421662199 55470271119815345132493299)
    ·
      refine ⟨83205406679723017698739949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55470271119815345132493299 83205406679723017698739949)
      ·
        refine ⟨31202027504896131637027481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83205406679723017698739949 31202027504896131637027481)
        ·
          refine ⟨23401520628672098727770611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31202027504896131637027481 23401520628672098727770611)
          ·
            refine ⟨35102280943008148091655917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23401520628672098727770611 35102280943008148091655917)
            ·
              refine ⟨13163355353628055534370969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35102280943008148091655917 13163355353628055534370969)
              ·
                refine ⟨9872516515221041650778227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13163355353628055534370969 9872516515221041650778227)
                ·
                  refine ⟨14808774772831562476167341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872516515221041650778227 14808774772831562476167341)
                  ·
                    refine ⟨5553290539811835928562753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14808774772831562476167341 5553290539811835928562753)
                    ·
                      refine ⟨4164967904858876946422065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553290539811835928562753 4164967904858876946422065)
                      ·
                        rfl

theorem cell23_8111246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_8111246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111246 prefixEnd_8111246 := by exact prefixLift 8111246
  have htrace : WordTrace (prefixWord ++ tailWord_8111246) baseStart_8111246 baseEnd_8111246 := by
    simpa [prefixWord, tailWord_8111246, baseEnd_8111246] using wordTrace_append hprefix tailTrace_8111246
  have hstable : (prefixWord ++ tailWord_8111246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111246).length < 2 ^ (prefixWord ++ tailWord_8111246).sum := by decide
  have hdescent : baseEnd_8111246 < baseStart_8111246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111263 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 1, 3, 2]
def baseStart_8111263 : Nat := 118140960795 + 8111263 * 2 ^ 59
def prefixEnd_8111263 : Nat := 4983230072969 + 3 ^ 40 * 8111263 * 2
def baseEnd_8111263 : Nat := 4164976634030003379909487

theorem tailTrace_8111263 : CollatzResearch.WordTrace tailWord_8111263 prefixEnd_8111263 4164976634030003379909487 := by
  unfold tailWord_8111263
  simp only [CollatzResearch.WordTrace]
  refine ⟨295842066013286919276666443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197228044008857946184444295 295842066013286919276666443)
  ·
    refine ⟨443763099019930378914999665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295842066013286919276666443 443763099019930378914999665)
    ·
      refine ⟨332822324264947784186249749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443763099019930378914999665 332822324264947784186249749)
      ·
        refine ⟨15601046449919427383730457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332822324264947784186249749 15601046449919427383730457)
        ·
          refine ⟨11700784837439570537797843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15601046449919427383730457 11700784837439570537797843)
          ·
            refine ⟨17551177256159355806696765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700784837439570537797843 17551177256159355806696765)
            ·
              refine ⟨6581691471059758427511287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17551177256159355806696765 6581691471059758427511287)
              ·
                refine ⟨9872537206589637641266931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581691471059758427511287 9872537206589637641266931)
                ·
                  refine ⟨14808805809884456461900397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872537206589637641266931 14808805809884456461900397)
                  ·
                    refine ⟨5553302178706671173212649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14808805809884456461900397 5553302178706671173212649)
                    ·
                      refine ⟨4164976634030003379909487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553302178706671173212649 4164976634030003379909487)
                      ·
                        rfl

theorem cell23_8111263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_8111263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111263 prefixEnd_8111263 := by exact prefixLift 8111263
  have htrace : WordTrace (prefixWord ++ tailWord_8111263) baseStart_8111263 baseEnd_8111263 := by
    simpa [prefixWord, tailWord_8111263, baseEnd_8111263] using wordTrace_append hprefix tailTrace_8111263
  have hstable : (prefixWord ++ tailWord_8111263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111263).length < 2 ^ (prefixWord ++ tailWord_8111263).sum := by decide
  have hdescent : baseEnd_8111263 < baseStart_8111263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111286 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_8111286 : Nat := 118140960795 + 8111286 * 2 ^ 59
def prefixEnd_8111286 : Nat := 4983230072969 + 3 ^ 40 * 8111286 * 2
def baseEnd_8111286 : Nat := 1388329481361685596640627

theorem tailTrace_8111286 : CollatzResearch.WordTrace tailWord_8111286 prefixEnd_8111286 1388329481361685596640627 := by
  unfold tailWord_8111286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490181555762724637797107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197228603261469062803169141 18490181555762724637797107)
  ·
    refine ⟨27735272333644086956695661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18490181555762724637797107 27735272333644086956695661)
    ·
      refine ⟨10400727125116532608760873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27735272333644086956695661 10400727125116532608760873)
      ·
        refine ⟨7800545343837399456570655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10400727125116532608760873 7800545343837399456570655)
        ·
          refine ⟨11700818015756099184855983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800545343837399456570655 11700818015756099184855983)
          ·
            refine ⟨17551227023634148777283975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700818015756099184855983 17551227023634148777283975)
            ·
              refine ⟨26326840535451223165925963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17551227023634148777283975 26326840535451223165925963)
              ·
                refine ⟨39490260803176834748888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26326840535451223165925963 39490260803176834748888945)
                ·
                  refine ⟨29617695602382626061666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39490260803176834748888945 29617695602382626061666709)
                  ·
                    refine ⟨1388329481361685596640627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29617695602382626061666709 1388329481361685596640627)
                    ·
                      rfl

theorem cell23_8111286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_8111286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111286 prefixEnd_8111286 := by exact prefixLift 8111286
  have htrace : WordTrace (prefixWord ++ tailWord_8111286) baseStart_8111286 baseEnd_8111286 := by
    simpa [prefixWord, tailWord_8111286, baseEnd_8111286] using wordTrace_append hprefix tailTrace_8111286
  have hstable : (prefixWord ++ tailWord_8111286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111286).length < 2 ^ (prefixWord ++ tailWord_8111286).sum := by decide
  have hdescent : baseEnd_8111286 < baseStart_8111286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111292 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_8111292 : Nat := 118140960795 + 8111292 * 2 ^ 59
def prefixEnd_8111292 : Nat := 4983230072969 + 3 ^ 40 * 8111292 * 2
def baseEnd_8111292 : Nat := 4164991524968983766446853

theorem tailTrace_8111292 : CollatzResearch.WordTrace tailWord_8111292 prefixEnd_8111292 4164991524968983766446853 := by
  unfold tailWord_8111292
  simp only [CollatzResearch.WordTrace]
  refine ⟨147921561865090928614736065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197228749153454571486314753 147921561865090928614736065)
  ·
    refine ⟨110941171398818196461052049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147921561865090928614736065 110941171398818196461052049)
    ·
      refine ⟨83205878549113647345789037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110941171398818196461052049 83205878549113647345789037)
      ·
        refine ⟨31202204455917617754670889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83205878549113647345789037 31202204455917617754670889)
        ·
          refine ⟨23401653341938213316003167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31202204455917617754670889 23401653341938213316003167)
          ·
            refine ⟨35102480012907319974004751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23401653341938213316003167 35102480012907319974004751)
            ·
              refine ⟨52653720019360979961007127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35102480012907319974004751 52653720019360979961007127)
              ·
                refine ⟨78980580029041469941510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52653720019360979961007127 78980580029041469941510691)
                ·
                  refine ⟨118470870043562204912266037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78980580029041469941510691 118470870043562204912266037)
                  ·
                    refine ⟨11106644066583956710524941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118470870043562204912266037 11106644066583956710524941)
                    ·
                      refine ⟨4164991524968983766446853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106644066583956710524941 4164991524968983766446853)
                      ·
                        rfl

theorem cell23_8111292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_8111292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111292 prefixEnd_8111292 := by exact prefixLift 8111292
  have htrace : WordTrace (prefixWord ++ tailWord_8111292) baseStart_8111292 baseEnd_8111292 := by
    simpa [prefixWord, tailWord_8111292, baseEnd_8111292] using wordTrace_append hprefix tailTrace_8111292
  have hstable : (prefixWord ++ tailWord_8111292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111292).length < 2 ^ (prefixWord ++ tailWord_8111292).sum := by decide
  have hdescent : baseEnd_8111292 < baseStart_8111292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111295 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 4, 5]
def baseStart_8111295 : Nat := 118140960795 + 8111295 * 2 ^ 59
def prefixEnd_8111295 : Nat := 4983230072969 + 3 ^ 40 * 8111295 * 2
def baseEnd_8111295 : Nat := 1388331021803649084903113

theorem tailTrace_8111295 : CollatzResearch.WordTrace tailWord_8111295 prefixEnd_8111295 1388331021803649084903113 := by
  unfold tailWord_8111295
  simp only [CollatzResearch.WordTrace]
  refine ⟨295843233149170988741831339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197228822099447325827887559 295843233149170988741831339)
  ·
    refine ⟨443764849723756483112747009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295843233149170988741831339 443764849723756483112747009)
    ·
      refine ⟨332823637292817362334560257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443764849723756483112747009 332823637292817362334560257)
      ·
        refine ⟨249617727969613021750920193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332823637292817362334560257 249617727969613021750920193)
        ·
          refine ⟨187213295977209766313190145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249617727969613021750920193 187213295977209766313190145)
          ·
            refine ⟨140409971982907324734892609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187213295977209766313190145 140409971982907324734892609)
            ·
              refine ⟨105307478987180493551169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140409971982907324734892609 105307478987180493551169457)
              ·
                refine ⟨78980609240385370163377093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105307478987180493551169457 78980609240385370163377093)
                ·
                  refine ⟨14808864232572256905633205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78980609240385370163377093 14808864232572256905633205)
                  ·
                    refine ⟨1388331021803649084903113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14808864232572256905633205 1388331021803649084903113)
                    ·
                      rfl

theorem cell23_8111295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_8111295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111295 prefixEnd_8111295 := by exact prefixLift 8111295
  have htrace : WordTrace (prefixWord ++ tailWord_8111295) baseStart_8111295 baseEnd_8111295 := by
    simpa [prefixWord, tailWord_8111295, baseEnd_8111295] using wordTrace_append hprefix tailTrace_8111295
  have hstable : (prefixWord ++ tailWord_8111295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111295).length < 2 ^ (prefixWord ++ tailWord_8111295).sum := by decide
  have hdescent : baseEnd_8111295 < baseStart_8111295 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111315 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_8111315 : Nat := 118140960795 + 8111315 * 2 ^ 59
def prefixEnd_8111315 : Nat := 4983230072969 + 3 ^ 40 * 8111315 * 2
def baseEnd_8111315 : Nat := 4165003335024037176459247

theorem tailTrace_8111315 : CollatzResearch.WordTrace tailWord_8111315 prefixEnd_8111315 4165003335024037176459247 := by
  unfold tailWord_8111315
  simp only [CollatzResearch.WordTrace]
  refine ⟨295843962609098532157559399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197229308406065688105039599 295843962609098532157559399)
  ·
    refine ⟨443765943913647798236339099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295843962609098532157559399 443765943913647798236339099)
    ·
      refine ⟨665648915870471697354508649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443765943913647798236339099 665648915870471697354508649)
      ·
        refine ⟨499236686902853773015881487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665648915870471697354508649 499236686902853773015881487)
        ·
          refine ⟨748855030354280659523822231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499236686902853773015881487 748855030354280659523822231)
          ·
            refine ⟨1123282545531420989285733347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748855030354280659523822231 1123282545531420989285733347)
            ·
              refine ⟨1684923818297131483928600021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123282545531420989285733347 1684923818297131483928600021)
              ·
                refine ⟨39490401991339019154576563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1684923818297131483928600021 39490401991339019154576563)
                ·
                  refine ⟨59235602987008528731864845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39490401991339019154576563 59235602987008528731864845)
                  ·
                    refine ⟨22213351120128198274449317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59235602987008528731864845 22213351120128198274449317)
                    ·
                      refine ⟨4165003335024037176459247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22213351120128198274449317 4165003335024037176459247)
                      ·
                        rfl

theorem cell23_8111315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_8111315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111315 prefixEnd_8111315 := by exact prefixLift 8111315
  have htrace : WordTrace (prefixWord ++ tailWord_8111315) baseStart_8111315 baseEnd_8111315 := by
    simpa [prefixWord, tailWord_8111315, baseEnd_8111315] using wordTrace_append hprefix tailTrace_8111315
  have hstable : (prefixWord ++ tailWord_8111315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111315).length < 2 ^ (prefixWord ++ tailWord_8111315).sum := by decide
  have hdescent : baseEnd_8111315 < baseStart_8111315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111332 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_8111332 : Nat := 118140960795 + 8111332 * 2 ^ 59
def prefixEnd_8111332 : Nat := 4983230072969 + 3 ^ 40 * 8111332 * 2
def baseEnd_8111332 : Nat := 4165012064195163609946669

theorem tailTrace_8111332 : CollatzResearch.WordTrace tailWord_8111332 prefixEnd_8111332 4165012064195163609946669 := by
  unfold tailWord_8111332
  simp only [CollatzResearch.WordTrace]
  refine ⟨147922291325018472030464125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197229721766691296040618833 147922291325018472030464125)
  ·
    refine ⟨55470859246881927011424047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147922291325018472030464125 55470859246881927011424047)
    ·
      refine ⟨83206288870322890517136071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55470859246881927011424047 83206288870322890517136071)
      ·
        refine ⟨124809433305484335775704107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83206288870322890517136071 124809433305484335775704107)
        ·
          refine ⟨187214149958226503663556161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124809433305484335775704107 187214149958226503663556161)
          ·
            refine ⟨140410612468669877747667121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187214149958226503663556161 140410612468669877747667121)
            ·
              refine ⟨105307959351502408310750341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140410612468669877747667121 105307959351502408310750341)
              ·
                refine ⟨19745242378406701558265689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105307959351502408310750341 19745242378406701558265689)
                ·
                  refine ⟨14808931783805026168699267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19745242378406701558265689 14808931783805026168699267)
                  ·
                    refine ⟨22213397675707539253048901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14808931783805026168699267 22213397675707539253048901)
                    ·
                      refine ⟨4165012064195163609946669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22213397675707539253048901 4165012064195163609946669)
                      ·
                        rfl

theorem cell23_8111332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_8111332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111332 prefixEnd_8111332 := by exact prefixLift 8111332
  have htrace : WordTrace (prefixWord ++ tailWord_8111332) baseStart_8111332 baseEnd_8111332 := by
    simpa [prefixWord, tailWord_8111332, baseEnd_8111332] using wordTrace_append hprefix tailTrace_8111332
  have hstable : (prefixWord ++ tailWord_8111332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111332).length < 2 ^ (prefixWord ++ tailWord_8111332).sum := by decide
  have hdescent : baseEnd_8111332 < baseStart_8111332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111345 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_8111345 : Nat := 118140960795 + 8111345 * 2 ^ 59
def prefixEnd_8111345 : Nat := 4983230072969 + 3 ^ 40 * 8111345 * 2
def baseEnd_8111345 : Nat := 4165018739443672059084109

theorem tailTrace_8111345 : CollatzResearch.WordTrace tailWord_8111345 prefixEnd_8111345 4165018739443672059084109 := by
  unfold tailWord_8111345
  simp only [CollatzResearch.WordTrace]
  refine ⟨295845056798989847281151489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197230037865993231520767659 295845056798989847281151489)
  ·
    refine ⟨221883792599242385460863617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295845056798989847281151489 221883792599242385460863617)
    ·
      refine ⟨166412844449431789095647713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221883792599242385460863617 166412844449431789095647713)
      ·
        refine ⟨124809633337073841821735785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166412844449431789095647713 124809633337073841821735785)
        ·
          refine ⟨93607225002805381366301839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124809633337073841821735785 93607225002805381366301839)
          ·
            refine ⟨140410837504208072049452759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93607225002805381366301839 140410837504208072049452759)
            ·
              refine ⟨210616256256312108074179139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140410837504208072049452759 210616256256312108074179139)
              ·
                refine ⟨315924384384468162111268709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210616256256312108074179139 315924384384468162111268709)
                ·
                  refine ⟨59235822072087780395862883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315924384384468162111268709 59235822072087780395862883)
                  ·
                    refine ⟨88853733108131670593794325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59235822072087780395862883 88853733108131670593794325)
                    ·
                      refine ⟨4165018739443672059084109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88853733108131670593794325 4165018739443672059084109)
                      ·
                        rfl

theorem cell23_8111345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_8111345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111345 prefixEnd_8111345 := by exact prefixLift 8111345
  have htrace : WordTrace (prefixWord ++ tailWord_8111345) baseStart_8111345 baseEnd_8111345 := by
    simpa [prefixWord, tailWord_8111345, baseEnd_8111345] using wordTrace_append hprefix tailTrace_8111345
  have hstable : (prefixWord ++ tailWord_8111345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111345).length < 2 ^ (prefixWord ++ tailWord_8111345).sum := by decide
  have hdescent : baseEnd_8111345 < baseStart_8111345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111436 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_8111436 : Nat := 118140960795 + 8111436 * 2 ^ 59
def prefixEnd_8111436 : Nat := 4983230072969 + 3 ^ 40 * 8111436 * 2
def baseEnd_8111436 : Nat := 1388355155394410401015397

theorem tailTrace_8111436 : CollatzResearch.WordTrace tailWord_8111436 prefixEnd_8111436 1388355155394410401015397 := by
  unfold tailWord_8111436
  simp only [CollatzResearch.WordTrace]
  refine ⟨147924187920830084911357081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197232250561106779881809441 147924187920830084911357081)
  ·
    refine ⟨110943140940622563683517811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147924187920830084911357081 110943140940622563683517811)
    ·
      refine ⟨166414711410933845525276717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110943140940622563683517811 166414711410933845525276717)
      ·
        refine ⟨62405516779100192071978769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166414711410933845525276717 62405516779100192071978769)
        ·
          refine ⟨46804137584325144053984077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62405516779100192071978769 46804137584325144053984077)
          ·
            refine ⟨17551551594121929020244029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46804137584325144053984077 17551551594121929020244029)
            ·
              refine ⟨6581831847795723382591511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17551551594121929020244029 6581831847795723382591511)
              ·
                refine ⟨9872747771693585073887267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581831847795723382591511 9872747771693585073887267)
                ·
                  refine ⟨14809121657540377610830901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872747771693585073887267 14809121657540377610830901)
                  ·
                    refine ⟨1388355155394410401015397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14809121657540377610830901 1388355155394410401015397)
                    ·
                      rfl

theorem cell23_8111436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_8111436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111436 prefixEnd_8111436 := by exact prefixLift 8111436
  have htrace : WordTrace (prefixWord ++ tailWord_8111436) baseStart_8111436 baseEnd_8111436 := by
    simpa [prefixWord, tailWord_8111436, baseEnd_8111436] using wordTrace_append hprefix tailTrace_8111436
  have hstable : (prefixWord ++ tailWord_8111436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111436).length < 2 ^ (prefixWord ++ tailWord_8111436).sum := by decide
  have hdescent : baseEnd_8111436 < baseStart_8111436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111449 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_8111449 : Nat := 118140960795 + 8111449 * 2 ^ 59
def prefixEnd_8111449 : Nat := 4983230072969 + 3 ^ 40 * 8111449 * 2
def baseEnd_8111449 : Nat := 1388357380477246550727877

theorem tailTrace_8111449 : CollatzResearch.WordTrace tailWord_8111449 prefixEnd_8111449 1388357380477246550727877 := by
  unfold tailWord_8111449
  simp only [CollatzResearch.WordTrace]
  refine ⟨295848849990613073042937401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197232566660408715361958267 295848849990613073042937401)
  ·
    refine ⟨221886637492959804782203051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295848849990613073042937401 221886637492959804782203051)
    ·
      refine ⟨332829956239439707173304577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221886637492959804782203051 332829956239439707173304577)
      ·
        refine ⟨249622467179579780379978433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332829956239439707173304577 249622467179579780379978433)
        ·
          refine ⟨187216850384684835284983825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249622467179579780379978433 187216850384684835284983825)
          ·
            refine ⟨140412637788513626463737869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187216850384684835284983825 140412637788513626463737869)
            ·
              refine ⟨52654739170692609923901701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140412637788513626463737869 52654739170692609923901701)
              ·
                refine ⟨9872763594504864360731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52654739170692609923901701 9872763594504864360731569)
                ·
                  refine ⟨7404572695878648270548677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872763594504864360731569 7404572695878648270548677)
                  ·
                    refine ⟨1388357380477246550727877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7404572695878648270548677 1388357380477246550727877)
                    ·
                      rfl

theorem cell23_8111449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_8111449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111449 prefixEnd_8111449 := by exact prefixLift 8111449
  have htrace : WordTrace (prefixWord ++ tailWord_8111449) baseStart_8111449 baseEnd_8111449 := by
    simpa [prefixWord, tailWord_8111449, baseEnd_8111449] using wordTrace_append hprefix tailTrace_8111449
  have hstable : (prefixWord ++ tailWord_8111449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111449).length < 2 ^ (prefixWord ++ tailWord_8111449).sum := by decide
  have hdescent : baseEnd_8111449 < baseStart_8111449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111459 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3]
def baseStart_8111459 : Nat := 118140960795 + 8111459 * 2 ^ 59
def prefixEnd_8111459 : Nat := 4983230072969 + 3 ^ 40 * 8111459 * 2
def baseEnd_8111459 : Nat := 4165077276238284613058585

theorem tailTrace_8111459 : CollatzResearch.WordTrace tailWord_8111459 prefixEnd_8111459 4165077276238284613058585 := by
  unfold tailWord_8111459
  simp only [CollatzResearch.WordTrace]
  refine ⟨295849214720576844750801431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197232809813717896500534287 295849214720576844750801431)
  ·
    refine ⟨443773822080865267126202147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295849214720576844750801431 443773822080865267126202147)
    ·
      refine ⟨665660733121297900689303221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443773822080865267126202147 665660733121297900689303221)
      ·
        refine ⟨62405693730121678189622177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 665660733121297900689303221 62405693730121678189622177)
        ·
          refine ⟨46804270297591258642216633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62405693730121678189622177 46804270297591258642216633)
          ·
            refine ⟨35103202723193443981662475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46804270297591258642216633 35103202723193443981662475)
            ·
              refine ⟨52654804084790165972493713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35103202723193443981662475 52654804084790165972493713)
              ·
                refine ⟨39491103063592624479370285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52654804084790165972493713 39491103063592624479370285)
                ·
                  refine ⟨14809163648847234179763857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39491103063592624479370285 14809163648847234179763857)
                  ·
                    refine ⟨11106872736635425634822893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14809163648847234179763857 11106872736635425634822893)
                    ·
                      refine ⟨4165077276238284613058585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106872736635425634822893 4165077276238284613058585)
                      ·
                        rfl

theorem cell23_8111459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_8111459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111459 prefixEnd_8111459 := by exact prefixLift 8111459
  have htrace : WordTrace (prefixWord ++ tailWord_8111459) baseStart_8111459 baseEnd_8111459 := by
    simpa [prefixWord, tailWord_8111459, baseEnd_8111459] using wordTrace_append hprefix tailTrace_8111459
  have hstable : (prefixWord ++ tailWord_8111459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111459).length < 2 ^ (prefixWord ++ tailWord_8111459).sum := by decide
  have hdescent : baseEnd_8111459 < baseStart_8111459 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111466 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_8111466 : Nat := 118140960795 + 8111466 * 2 ^ 59
def prefixEnd_8111466 : Nat := 4983230072969 + 3 ^ 40 * 8111466 * 2
def baseEnd_8111466 : Nat := 1388360290200955361890351

theorem tailTrace_8111466 : CollatzResearch.WordTrace tailWord_8111466 prefixEnd_8111466 1388360290200955361890351 := by
  unfold tailWord_8111466
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962367507887871236576563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197232980021034323297537501 73962367507887871236576563)
  ·
    refine ⟨110943551261831806854864845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73962367507887871236576563 110943551261831806854864845)
    ·
      refine ⟨41603831723186927570574317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110943551261831806854864845 41603831723186927570574317)
      ·
        refine ⟨15601436896195097838965369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41603831723186927570574317 15601436896195097838965369)
        ·
          refine ⟨11701077672146323379224027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15601436896195097838965369 11701077672146323379224027)
          ·
            refine ⟨17551616508219485068836041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701077672146323379224027 17551616508219485068836041)
            ·
              refine ⟨13163712381164613801627031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17551616508219485068836041 13163712381164613801627031)
              ·
                refine ⟨19745568571746920702440547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13163712381164613801627031 19745568571746920702440547)
                ·
                  refine ⟨29618352857620381053660821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19745568571746920702440547 29618352857620381053660821)
                  ·
                    refine ⟨1388360290200955361890351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29618352857620381053660821 1388360290200955361890351)
                    ·
                      rfl

theorem cell23_8111466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_8111466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111466 prefixEnd_8111466 := by exact prefixLift 8111466
  have htrace : WordTrace (prefixWord ++ tailWord_8111466) baseStart_8111466 baseEnd_8111466 := by
    simpa [prefixWord, tailWord_8111466, baseEnd_8111466] using wordTrace_append hprefix tailTrace_8111466
  have hstable : (prefixWord ++ tailWord_8111466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111466).length < 2 ^ (prefixWord ++ tailWord_8111466).sum := by decide
  have hdescent : baseEnd_8111466 < baseStart_8111466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111469 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_8111469 : Nat := 118140960795 + 8111469 * 2 ^ 59
def prefixEnd_8111469 : Nat := 4983230072969 + 3 ^ 40 * 8111469 * 2
def baseEnd_8111469 : Nat := 4165082411044829573933539

theorem tailTrace_8111469 : CollatzResearch.WordTrace tailWord_8111469 prefixEnd_8111469 4165082411044829573933539 := by
  unfold tailWord_8111469
  simp only [CollatzResearch.WordTrace]
  refine ⟨295849579450540616458665461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197233052967027077639110307 295849579450540616458665461)
  ·
    refine ⟨27735898073488182792999887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295849579450540616458665461 27735898073488182792999887)
    ·
      refine ⟨41603847110232274189499831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27735898073488182792999887 41603847110232274189499831)
      ·
        refine ⟨62405770665348411284249747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41603847110232274189499831 62405770665348411284249747)
        ·
          refine ⟨93608655998022616926374621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62405770665348411284249747 93608655998022616926374621)
          ·
            refine ⟨35103245999258481347390483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93608655998022616926374621 35103245999258481347390483)
            ·
              refine ⟨52654868998887722021085725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35103245999258481347390483 52654868998887722021085725)
              ·
                refine ⟨19745575874582895757907147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52654868998887722021085725 19745575874582895757907147)
                ·
                  refine ⟨29618363811874343636860721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19745575874582895757907147 29618363811874343636860721)
                  ·
                    refine ⟨22213772858905757727645541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29618363811874343636860721 22213772858905757727645541)
                    ·
                      refine ⟨4165082411044829573933539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22213772858905757727645541 4165082411044829573933539)
                      ·
                        rfl

theorem cell23_8111469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_8111469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111469 prefixEnd_8111469 := by exact prefixLift 8111469
  have htrace : WordTrace (prefixWord ++ tailWord_8111469) baseStart_8111469 baseEnd_8111469 := by
    simpa [prefixWord, tailWord_8111469, baseEnd_8111469] using wordTrace_append hprefix tailTrace_8111469
  have hstable : (prefixWord ++ tailWord_8111469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111469).length < 2 ^ (prefixWord ++ tailWord_8111469).sum := by decide
  have hdescent : baseEnd_8111469 < baseStart_8111469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111490 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_8111490 : Nat := 118140960795 + 8111490 * 2 ^ 59
def prefixEnd_8111490 : Nat := 4983230072969 + 3 ^ 40 * 8111490 * 2
def baseEnd_8111490 : Nat := 4165093194138573991770943

theorem tailTrace_8111490 : CollatzResearch.WordTrace tailWord_8111490 prefixEnd_8111490 4165093194138573991770943 := by
  unfold tailWord_8111490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962586345866134261294981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197233563588976358030119949 73962586345866134261294981)
  ·
    refine ⟨13867984939849900173992809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73962586345866134261294981 13867984939849900173992809)
    ·
      refine ⟨10400988704887425130494607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13867984939849900173992809 10400988704887425130494607)
      ·
        refine ⟨15601483057331137695741911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400988704887425130494607 15601483057331137695741911)
        ·
          refine ⟨23402224585996706543612867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15601483057331137695741911 23402224585996706543612867)
          ·
            refine ⟨35103336878995059815419301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23402224585996706543612867 35103336878995059815419301)
            ·
              refine ⟨6581875664811573715391119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35103336878995059815419301 6581875664811573715391119)
              ·
                refine ⟨9872813497217360573086679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581875664811573715391119 9872813497217360573086679)
                ·
                  refine ⟨14809220245826040859630019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872813497217360573086679 14809220245826040859630019)
                  ·
                    refine ⟨22213830368739061289445029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14809220245826040859630019 22213830368739061289445029)
                    ·
                      refine ⟨4165093194138573991770943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22213830368739061289445029 4165093194138573991770943)
                      ·
                        rfl

theorem cell23_8111490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_8111490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111490 prefixEnd_8111490 := by exact prefixLift 8111490
  have htrace : WordTrace (prefixWord ++ tailWord_8111490) baseStart_8111490 baseEnd_8111490 := by
    simpa [prefixWord, tailWord_8111490, baseEnd_8111490] using wordTrace_append hprefix tailTrace_8111490
  have hstable : (prefixWord ++ tailWord_8111490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111490).length < 2 ^ (prefixWord ++ tailWord_8111490).sum := by decide
  have hdescent : baseEnd_8111490 < baseStart_8111490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111523 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 2, 1, 3]
def baseStart_8111523 : Nat := 118140960795 + 8111523 * 2 ^ 59
def prefixEnd_8111523 : Nat := 4983230072969 + 3 ^ 40 * 8111523 * 2
def baseEnd_8111523 : Nat := 4165110139000172362658291

theorem tailTrace_8111523 : CollatzResearch.WordTrace tailWord_8111523 prefixEnd_8111523 4165110139000172362658291 := by
  unfold tailWord_8111523
  simp only [CollatzResearch.WordTrace]
  refine ⟨295851548992344983681131223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197234365994896655787420815 295851548992344983681131223)
  ·
    refine ⟨443777323488517475521696835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295851548992344983681131223 443777323488517475521696835)
    ·
      refine ⟨665665985232776213282545253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443777323488517475521696835 665665985232776213282545253)
      ·
        refine ⟨124812372231145539990477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665665985232776213282545253 124812372231145539990477235)
        ·
          refine ⟨187218558346718309985715853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124812372231145539990477235 187218558346718309985715853)
          ·
            refine ⟨70206959380019366244643445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187218558346718309985715853 70206959380019366244643445)
            ·
              refine ⟨6581902441876815585435323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70206959380019366244643445 6581902441876815585435323)
              ·
                refine ⟨9872853662815223378152985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581902441876815585435323 9872853662815223378152985)
                ·
                  refine ⟨7404640247111417533614739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872853662815223378152985 7404640247111417533614739)
                  ·
                    refine ⟨11106960370667126300422109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404640247111417533614739 11106960370667126300422109)
                    ·
                      refine ⟨4165110139000172362658291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11106960370667126300422109 4165110139000172362658291)
                      ·
                        rfl

theorem cell23_8111523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_8111523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111523 prefixEnd_8111523 := by exact prefixLift 8111523
  have htrace : WordTrace (prefixWord ++ tailWord_8111523) baseStart_8111523 baseEnd_8111523 := by
    simpa [prefixWord, tailWord_8111523, baseEnd_8111523] using wordTrace_append hprefix tailTrace_8111523
  have hstable : (prefixWord ++ tailWord_8111523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111523).length < 2 ^ (prefixWord ++ tailWord_8111523).sum := by decide
  have hdescent : baseEnd_8111523 < baseStart_8111523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111549 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_8111549 : Nat := 118140960795 + 8111549 * 2 ^ 59
def prefixEnd_8111549 : Nat := 4983230072969 + 3 ^ 40 * 8111549 * 2
def baseEnd_8111549 : Nat := 4165123489497189260933171

theorem tailTrace_8111549 : CollatzResearch.WordTrace tailWord_8111549 prefixEnd_8111549 4165123489497189260933171 := by
  unfold tailWord_8111549
  simp only [CollatzResearch.WordTrace]
  refine ⟨295852497290250790121577701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197234998193500526747718467 295852497290250790121577701)
  ·
    refine ⟨55472343241922023147795819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295852497290250790121577701 55472343241922023147795819)
    ·
      refine ⟨83208514862883034721693729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55472343241922023147795819 83208514862883034721693729)
      ·
        refine ⟨62406386147162276041270297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83208514862883034721693729 62406386147162276041270297)
        ·
          refine ⟨46804789610371707030952723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62406386147162276041270297 46804789610371707030952723)
          ·
            refine ⟨70207184415557560546429085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46804789610371707030952723 70207184415557560546429085)
            ·
              refine ⟨26327694155834085204910907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70207184415557560546429085 26327694155834085204910907)
              ·
                refine ⟨39491541233751127807366361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26327694155834085204910907 39491541233751127807366361)
                ·
                  refine ⟨29618655925313345855524771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39491541233751127807366361 29618655925313345855524771)
                  ·
                    refine ⟨44427983887970018783287157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29618655925313345855524771 44427983887970018783287157)
                    ·
                      refine ⟨4165123489497189260933171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44427983887970018783287157 4165123489497189260933171)
                      ·
                        rfl

theorem cell23_8111549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_8111549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111549 prefixEnd_8111549 := by exact prefixLift 8111549
  have htrace : WordTrace (prefixWord ++ tailWord_8111549) baseStart_8111549 baseEnd_8111549 := by
    simpa [prefixWord, tailWord_8111549, baseEnd_8111549] using wordTrace_append hprefix tailTrace_8111549
  have hstable : (prefixWord ++ tailWord_8111549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111549).length < 2 ^ (prefixWord ++ tailWord_8111549).sum := by decide
  have hdescent : baseEnd_8111549 < baseStart_8111549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111552 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 9]
def baseStart_8111552 : Nat := 118140960795 + 8111552 * 2 ^ 59
def prefixEnd_8111552 : Nat := 4983230072969 + 3 ^ 40 * 8111552 * 2
def baseEnd_8111552 : Nat := 462791669993239194355073

theorem tailTrace_8111552 : CollatzResearch.WordTrace tailWord_8111552 prefixEnd_8111552 462791669993239194355073 := by
  unfold tailWord_8111552
  simp only [CollatzResearch.WordTrace]
  refine ⟨147926303354619960816968455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197235071139493281089291273 147926303354619960816968455)
  ·
    refine ⟨221889455031929941225452683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147926303354619960816968455 221889455031929941225452683)
    ·
      refine ⟨332834182547894911838179025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221889455031929941225452683 332834182547894911838179025)
      ·
        refine ⟨249625636910921183878634269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332834182547894911838179025 249625636910921183878634269)
        ·
          refine ⟨93609613841595443954487851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249625636910921183878634269 93609613841595443954487851)
          ·
            refine ⟨140414420762393165931731777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93609613841595443954487851 140414420762393165931731777)
            ·
              refine ⟨105310815571794874448798833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140414420762393165931731777 105310815571794874448798833)
              ·
                refine ⟨78983111678846155836599125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105310815571794874448798833 78983111678846155836599125)
                ·
                  refine ⟨462791669993239194355073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78983111678846155836599125 462791669993239194355073)
                  ·
                    rfl

theorem cell23_8111552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_8111552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111552 prefixEnd_8111552 := by exact prefixLift 8111552
  have htrace : WordTrace (prefixWord ++ tailWord_8111552) baseStart_8111552 baseEnd_8111552 := by
    simpa [prefixWord, tailWord_8111552, baseEnd_8111552] using wordTrace_append hprefix tailTrace_8111552
  have hstable : (prefixWord ++ tailWord_8111552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111552).length < 2 ^ (prefixWord ++ tailWord_8111552).sum := by decide
  have hdescent : baseEnd_8111552 < baseStart_8111552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111599 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 2, 5]
def baseStart_8111599 : Nat := 118140960795 + 8111599 * 2 ^ 59
def prefixEnd_8111599 : Nat := 4983230072969 + 3 ^ 40 * 8111599 * 2
def baseEnd_8111599 : Nat := 1388383054509971355102647

theorem tailTrace_8111599 : CollatzResearch.WordTrace tailWord_8111599 prefixEnd_8111599 1388383054509971355102647 := by
  unfold tailWord_8111599
  simp only [CollatzResearch.WordTrace]
  refine ⟨295854320940069648660897851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197236213960046432440598567 295854320940069648660897851)
  ·
    refine ⟨443781481410104472991346777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295854320940069648660897851 443781481410104472991346777)
    ·
      refine ⟨332836111057578354743510083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443781481410104472991346777 332836111057578354743510083)
      ·
        refine ⟨499254166586367532115265125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332836111057578354743510083 499254166586367532115265125)
        ·
          refine ⟨93610156234943912271612211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499254166586367532115265125 93610156234943912271612211)
          ·
            refine ⟨140415234352415868407418317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93610156234943912271612211 140415234352415868407418317)
            ·
              refine ⟨52655712882155950652781869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140415234352415868407418317 52655712882155950652781869)
              ·
                refine ⟨19745892330808481494793201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52655712882155950652781869 19745892330808481494793201)
                ·
                  refine ⟨14809419248106361121094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19745892330808481494793201 14809419248106361121094901)
                  ·
                    refine ⟨1388383054509971355102647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14809419248106361121094901 1388383054509971355102647)
                    ·
                      rfl

theorem cell23_8111599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_8111599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111599 prefixEnd_8111599 := by exact prefixLift 8111599
  have htrace : WordTrace (prefixWord ++ tailWord_8111599) baseStart_8111599 baseEnd_8111599 := by
    simpa [prefixWord, tailWord_8111599, baseEnd_8111599] using wordTrace_append hprefix tailTrace_8111599
  have hstable : (prefixWord ++ tailWord_8111599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111599).length < 2 ^ (prefixWord ++ tailWord_8111599).sum := by decide
  have hdescent : baseEnd_8111599 < baseStart_8111599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111614 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8111614 : Nat := 118140960795 + 8111614 * 2 ^ 59
def prefixEnd_8111614 : Nat := 4983230072969 + 3 ^ 40 * 8111614 * 2
def baseEnd_8111614 : Nat := 4165156865739731506620373

theorem tailTrace_8111614 : CollatzResearch.WordTrace tailWord_8111614 prefixEnd_8111614 4165156865739731506620373 := by
  unfold tailWord_8111614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36981858504376913277836737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197236578690010204148462597 36981858504376913277836737)
  ·
    refine ⟨27736393878282684958377553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36981858504376913277836737 27736393878282684958377553)
    ·
      refine ⟨20802295408712013718783165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27736393878282684958377553 20802295408712013718783165)
      ·
        refine ⟨7800860778267005144543687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20802295408712013718783165 7800860778267005144543687)
        ·
          refine ⟨11701291167400507716815531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7800860778267005144543687 11701291167400507716815531)
          ·
            refine ⟨17551936751100761575223297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701291167400507716815531 17551936751100761575223297)
            ·
              refine ⟨13163952563325571181417473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17551936751100761575223297 13163952563325571181417473)
              ·
                refine ⟨9872964422494178386063105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13163952563325571181417473 9872964422494178386063105)
                ·
                  refine ⟨7404723316870633789547329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9872964422494178386063105 7404723316870633789547329)
                  ·
                    refine ⟨5553542487652975342160497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7404723316870633789547329 5553542487652975342160497)
                    ·
                      refine ⟨4165156865739731506620373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553542487652975342160497 4165156865739731506620373)
                      ·
                        rfl

theorem cell23_8111614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8111614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111614 prefixEnd_8111614 := by exact prefixLift 8111614
  have htrace : WordTrace (prefixWord ++ tailWord_8111614) baseStart_8111614 baseEnd_8111614 := by
    simpa [prefixWord, tailWord_8111614, baseEnd_8111614] using wordTrace_append hprefix tailTrace_8111614
  have hstable : (prefixWord ++ tailWord_8111614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111614).length < 2 ^ (prefixWord ++ tailWord_8111614).sum := by decide
  have hdescent : baseEnd_8111614 < baseStart_8111614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111619 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4]
def baseStart_8111619 : Nat := 118140960795 + 8111619 * 2 ^ 59
def prefixEnd_8111619 : Nat := 4983230072969 + 3 ^ 40 * 8111619 * 2
def baseEnd_8111619 : Nat := 4165159433143003987057849

theorem tailTrace_8111619 : CollatzResearch.WordTrace tailWord_8111619 prefixEnd_8111619 4165159433143003987057849 := by
  unfold tailWord_8111619
  simp only [CollatzResearch.WordTrace]
  refine ⟨295855050399997192076625911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197236700266664794717750607 295855050399997192076625911)
  ·
    refine ⟨443782575599995788114938867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295855050399997192076625911 443782575599995788114938867)
    ·
      refine ⟨665673863399993682172408301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443782575599995788114938867 665673863399993682172408301)
      ·
        refine ⟨249627698774997630814653113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665673863399993682172408301 249627698774997630814653113)
        ·
          refine ⟨187220774081248223110989835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249627698774997630814653113 187220774081248223110989835)
          ·
            refine ⟨280831161121872334666484753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187220774081248223110989835 280831161121872334666484753)
            ·
              refine ⟨210623370841404250999863565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280831161121872334666484753 210623370841404250999863565)
              ·
                refine ⟨78983764065526594124948837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210623370841404250999863565 78983764065526594124948837)
                ·
                  refine ⟨14809455762286236398427907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78983764065526594124948837 14809455762286236398427907)
                  ·
                    refine ⟨22214183643429354597641861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14809455762286236398427907 22214183643429354597641861)
                    ·
                      refine ⟨4165159433143003987057849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22214183643429354597641861 4165159433143003987057849)
                      ·
                        rfl

theorem cell23_8111619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_8111619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111619 prefixEnd_8111619 := by exact prefixLift 8111619
  have htrace : WordTrace (prefixWord ++ tailWord_8111619) baseStart_8111619 baseEnd_8111619 := by
    simpa [prefixWord, tailWord_8111619, baseEnd_8111619] using wordTrace_append hprefix tailTrace_8111619
  have hstable : (prefixWord ++ tailWord_8111619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111619).length < 2 ^ (prefixWord ++ tailWord_8111619).sum := by decide
  have hdescent : baseEnd_8111619 < baseStart_8111619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111676 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 8]
def baseStart_8111676 : Nat := 118140960795 + 8111676 * 2 ^ 59
def prefixEnd_8111676 : Nat := 4983230072969 + 3 ^ 40 * 8111676 * 2
def baseEnd_8111676 : Nat := 462798744615590029338343

theorem tailTrace_8111676 : CollatzResearch.WordTrace tailWord_8111676 prefixEnd_8111676 462798744615590029338343 := by
  unfold tailWord_8111676
  simp only [CollatzResearch.WordTrace]
  refine ⟨147928564680395345405725441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197238086240527127207633921 147928564680395345405725441)
  ·
    refine ⟨110946423510296509054294081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147928564680395345405725441 110946423510296509054294081)
    ·
      refine ⟨83209817632722381790720561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110946423510296509054294081 83209817632722381790720561)
      ·
        refine ⟨62407363224541786343040421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83209817632722381790720561 62407363224541786343040421)
        ·
          refine ⟨11701380604601584939320079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62407363224541786343040421 11701380604601584939320079)
          ·
            refine ⟨17552070906902377408980119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701380604601584939320079 17552070906902377408980119)
            ·
              refine ⟨26328106360353566113470179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552070906902377408980119 26328106360353566113470179)
              ·
                refine ⟨39492159540530349170205269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26328106360353566113470179 39492159540530349170205269)
                ·
                  refine ⟨462798744615590029338343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39492159540530349170205269 462798744615590029338343)
                  ·
                    rfl

theorem cell23_8111676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_8111676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111676 prefixEnd_8111676 := by exact prefixLift 8111676
  have htrace : WordTrace (prefixWord ++ tailWord_8111676) baseStart_8111676 baseEnd_8111676 := by
    simpa [prefixWord, tailWord_8111676, baseEnd_8111676] using wordTrace_append hprefix tailTrace_8111676
  have hstable : (prefixWord ++ tailWord_8111676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111676).length < 2 ^ (prefixWord ++ tailWord_8111676).sum := by decide
  have hdescent : baseEnd_8111676 < baseStart_8111676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111679 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_8111679 : Nat := 118140960795 + 8111679 * 2 ^ 59
def prefixEnd_8111679 : Nat := 4983230072969 + 3 ^ 40 * 8111679 * 2
def baseEnd_8111679 : Nat := 4165190241982273752307573

theorem tailTrace_8111679 : CollatzResearch.WordTrace tailWord_8111679 prefixEnd_8111679 4165190241982273752307573 := by
  unfold tailWord_8111679
  simp only [CollatzResearch.WordTrace]
  refine ⟨295857238779779822323810091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197238159186519881549206727 295857238779779822323810091)
  ·
    refine ⟨443785858169669733485715137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295857238779779822323810091 443785858169669733485715137)
    ·
      refine ⟨332839393627252300114286353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443785858169669733485715137 332839393627252300114286353)
      ·
        refine ⟨249629545220439225085714765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332839393627252300114286353 249629545220439225085714765)
        ·
          refine ⟨93611079457664709407143037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249629545220439225085714765 93611079457664709407143037)
          ·
            refine ⟨35104154796624266027678639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93611079457664709407143037 35104154796624266027678639)
            ·
              refine ⟨52656232194936399041517959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35104154796624266027678639 52656232194936399041517959)
              ·
                refine ⟨78984348292404598562276939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52656232194936399041517959 78984348292404598562276939)
                ·
                  refine ⟨118476522438606897843415409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78984348292404598562276939 118476522438606897843415409)
                  ·
                    refine ⟨88857391828955173382561557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118476522438606897843415409 88857391828955173382561557)
                    ·
                      refine ⟨4165190241982273752307573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88857391828955173382561557 4165190241982273752307573)
                      ·
                        rfl

theorem cell23_8111679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_8111679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111679 prefixEnd_8111679 := by exact prefixLift 8111679
  have htrace : WordTrace (prefixWord ++ tailWord_8111679) baseStart_8111679 baseEnd_8111679 := by
    simpa [prefixWord, tailWord_8111679, baseEnd_8111679] using wordTrace_append hprefix tailTrace_8111679
  have hstable : (prefixWord ++ tailWord_8111679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111679).length < 2 ^ (prefixWord ++ tailWord_8111679).sum := by decide
  have hdescent : baseEnd_8111679 < baseStart_8111679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111689 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_8111689 : Nat := 118140960795 + 8111689 * 2 ^ 59
def prefixEnd_8111689 : Nat := 4983230072969 + 3 ^ 40 * 8111689 * 2
def baseEnd_8111689 : Nat := 1388398458929606237727509

theorem tailTrace_8111689 : CollatzResearch.WordTrace tailWord_8111689 prefixEnd_8111689 1388398458929606237727509 := by
  unfold tailWord_8111689
  simp only [CollatzResearch.WordTrace]
  refine ⟨295857603509743594031674121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197238402339829062687782747 295857603509743594031674121)
  ·
    refine ⟨221893202632307695523755591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295857603509743594031674121 221893202632307695523755591)
    ·
      refine ⟨332839803948461543285633387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221893202632307695523755591 332839803948461543285633387)
      ·
        refine ⟨499259705922692314928450081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332839803948461543285633387 499259705922692314928450081)
        ·
          refine ⟨374444779442019236196337561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499259705922692314928450081 374444779442019236196337561)
          ·
            refine ⟨280833584581514427147253171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374444779442019236196337561 280833584581514427147253171)
            ·
              refine ⟨421250376872271640720879757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280833584581514427147253171 421250376872271640720879757)
              ·
                refine ⟨157968891327101865270329909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421250376872271640720879757 157968891327101865270329909)
                ·
                  refine ⟨14809583561915799869093429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157968891327101865270329909 14809583561915799869093429)
                  ·
                    refine ⟨1388398458929606237727509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14809583561915799869093429 1388398458929606237727509)
                    ·
                      rfl

theorem cell23_8111689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_8111689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111689 prefixEnd_8111689 := by exact prefixLift 8111689
  have htrace : WordTrace (prefixWord ++ tailWord_8111689) baseStart_8111689 baseEnd_8111689 := by
    simpa [prefixWord, tailWord_8111689, baseEnd_8111689] using wordTrace_append hprefix tailTrace_8111689
  have hstable : (prefixWord ++ tailWord_8111689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111689).length < 2 ^ (prefixWord ++ tailWord_8111689).sum := by decide
  have hdescent : baseEnd_8111689 < baseStart_8111689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111696 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2]
def baseStart_8111696 : Nat := 118140960795 + 8111696 * 2 ^ 59
def prefixEnd_8111696 : Nat := 4983230072969 + 3 ^ 40 * 8111696 * 2
def baseEnd_8111696 : Nat := 4165198971153400185794995

theorem tailTrace_8111696 : CollatzResearch.WordTrace tailWord_8111696 prefixEnd_8111696 4165198971153400185794995 := by
  unfold tailWord_8111696
  simp only [CollatzResearch.WordTrace]
  refine ⟨147928929410359117113589471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197238572547145489484785961 147928929410359117113589471)
  ·
    refine ⟨221893394115538675670384207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147928929410359117113589471 221893394115538675670384207)
    ·
      refine ⟨332840091173308013505576311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221893394115538675670384207 332840091173308013505576311)
      ·
        refine ⟨499260136759962020258364467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332840091173308013505576311 499260136759962020258364467)
        ·
          refine ⟨748890205139943030387546701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499260136759962020258364467 748890205139943030387546701)
          ·
            refine ⟨280833826927478636395330013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748890205139943030387546701 280833826927478636395330013)
            ·
              refine ⟨105312685097804488648248755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280833826927478636395330013 105312685097804488648248755)
              ·
                refine ⟨157969027646706732972373133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105312685097804488648248755 157969027646706732972373133)
                ·
                  refine ⟨59238385367515024864639925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157969027646706732972373133 59238385367515024864639925)
                  ·
                    refine ⟨5553598628204533581059993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59238385367515024864639925 5553598628204533581059993)
                    ·
                      refine ⟨4165198971153400185794995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553598628204533581059993 4165198971153400185794995)
                      ·
                        rfl

theorem cell23_8111696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 3, 5, 2].length) (baseStart_8111696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111696 prefixEnd_8111696 := by exact prefixLift 8111696
  have htrace : WordTrace (prefixWord ++ tailWord_8111696) baseStart_8111696 baseEnd_8111696 := by
    simpa [prefixWord, tailWord_8111696, baseEnd_8111696] using wordTrace_append hprefix tailTrace_8111696
  have hstable : (prefixWord ++ tailWord_8111696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111696).length < 2 ^ (prefixWord ++ tailWord_8111696).sum := by decide
  have hdescent : baseEnd_8111696 < baseStart_8111696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111703 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_8111703 : Nat := 118140960795 + 8111703 * 2 ^ 59
def prefixEnd_8111703 : Nat := 4983230072969 + 3 ^ 40 * 8111703 * 2
def baseEnd_8111703 : Nat := 4165202565517981658407463

theorem tailTrace_8111703 : CollatzResearch.WordTrace tailWord_8111703 prefixEnd_8111703 4165202565517981658407463 := by
  unfold tailWord_8111703
  simp only [CollatzResearch.WordTrace]
  refine ⟨295858114131692874422683763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197238742754461916281789175 295858114131692874422683763)
  ·
    refine ⟨443787171197539311634025645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295858114131692874422683763 443787171197539311634025645)
    ·
      refine ⟨166420189199077241862759617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443787171197539311634025645 166420189199077241862759617)
      ·
        refine ⟨124815141899307931397069713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166420189199077241862759617 124815141899307931397069713)
        ·
          refine ⟨93611356424480948547802285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124815141899307931397069713 93611356424480948547802285)
          ·
            refine ⟨35104258659180355705425857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93611356424480948547802285 35104258659180355705425857)
            ·
              refine ⟨26328193994385266779069393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35104258659180355705425857 26328193994385266779069393)
              ·
                refine ⟨19746145495788950084302045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26328193994385266779069393 19746145495788950084302045)
                ·
                  refine ⟨7404804560920856281613267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19746145495788950084302045 7404804560920856281613267)
                  ·
                    refine ⟨11107206841381284422419901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404804560920856281613267 11107206841381284422419901)
                    ·
                      refine ⟨4165202565517981658407463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107206841381284422419901 4165202565517981658407463)
                      ·
                        rfl

theorem cell23_8111703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_8111703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111703 prefixEnd_8111703 := by exact prefixLift 8111703
  have htrace : WordTrace (prefixWord ++ tailWord_8111703) baseStart_8111703 baseEnd_8111703 := by
    simpa [prefixWord, tailWord_8111703, baseEnd_8111703] using wordTrace_append hprefix tailTrace_8111703
  have hstable : (prefixWord ++ tailWord_8111703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111703).length < 2 ^ (prefixWord ++ tailWord_8111703).sum := by decide
  have hdescent : baseEnd_8111703 < baseStart_8111703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111713 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_8111713 : Nat := 118140960795 + 8111713 * 2 ^ 59
def prefixEnd_8111713 : Nat := 4983230072969 + 3 ^ 40 * 8111713 * 2
def baseEnd_8111713 : Nat := 4165207700324526619282417

theorem tailTrace_8111713 : CollatzResearch.WordTrace tailWord_8111713 prefixEnd_8111713 4165207700324526619282417 := by
  unfold tailWord_8111713
  simp only [CollatzResearch.WordTrace]
  refine ⟨295858478861656646130547793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197238985907771097420365195 295858478861656646130547793)
  ·
    refine ⟨221893859146242484597910845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295858478861656646130547793 221893859146242484597910845)
    ·
      refine ⟨83210197179840931724216567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221893859146242484597910845 83210197179840931724216567)
      ·
        refine ⟨124815295769761397586324851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83210197179840931724216567 124815295769761397586324851)
        ·
          refine ⟨187222943654642096379487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124815295769761397586324851 187222943654642096379487277)
          ·
            refine ⟨70208603870490786142307729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187222943654642096379487277 70208603870490786142307729)
            ·
              refine ⟨52656452902868089606730797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70208603870490786142307729 52656452902868089606730797)
              ·
                refine ⟨19746169838575533602524049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52656452902868089606730797 19746169838575533602524049)
                ·
                  refine ⟨14809627378931650201893037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19746169838575533602524049 14809627378931650201893037)
                  ·
                    refine ⟨5553610267099368825709889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14809627378931650201893037 5553610267099368825709889)
                    ·
                      refine ⟨4165207700324526619282417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553610267099368825709889 4165207700324526619282417)
                      ·
                        rfl

theorem cell23_8111713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_8111713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111713 prefixEnd_8111713 := by exact prefixLift 8111713
  have htrace : WordTrace (prefixWord ++ tailWord_8111713) baseStart_8111713 baseEnd_8111713 := by
    simpa [prefixWord, tailWord_8111713, baseEnd_8111713] using wordTrace_append hprefix tailTrace_8111713
  have hstable : (prefixWord ++ tailWord_8111713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111713).length < 2 ^ (prefixWord ++ tailWord_8111713).sum := by decide
  have hdescent : baseEnd_8111713 < baseStart_8111713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111730 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_8111730 : Nat := 118140960795 + 8111730 * 2 ^ 59
def prefixEnd_8111730 : Nat := 4983230072969 + 3 ^ 40 * 8111730 * 2
def baseEnd_8111730 : Nat := 4165216429495653052769839

theorem tailTrace_8111730 : CollatzResearch.WordTrace tailWord_8111730 prefixEnd_8111730 4165216429495653052769839 := by
  unfold tailWord_8111730
  simp only [CollatzResearch.WordTrace]
  refine ⟨73964774725648764508479161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197239399268396705355944429 73964774725648764508479161)
  ·
    refine ⟨55473581044236573381359371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73964774725648764508479161 55473581044236573381359371)
    ·
      refine ⟨83210371566354860072039057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55473581044236573381359371 83210371566354860072039057)
      ·
        refine ⟨62407778674766145054029293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83210371566354860072039057 62407778674766145054029293)
        ·
          refine ⟨23402917003037304395260985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62407778674766145054029293 23402917003037304395260985)
          ·
            refine ⟨17552187752277978296445739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23402917003037304395260985 17552187752277978296445739)
            ·
              refine ⟨26328281628416967444668609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552187752277978296445739 26328281628416967444668609)
              ·
                refine ⟨19746211221312725583501457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26328281628416967444668609 19746211221312725583501457)
                ·
                  refine ⟨14809658415984544187626093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19746211221312725583501457 14809658415984544187626093)
                  ·
                    refine ⟨5553621905994204070359785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14809658415984544187626093 5553621905994204070359785)
                    ·
                      refine ⟨4165216429495653052769839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553621905994204070359785 4165216429495653052769839)
                      ·
                        rfl

theorem cell23_8111730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_8111730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111730 prefixEnd_8111730 := by exact prefixLift 8111730
  have htrace : WordTrace (prefixWord ++ tailWord_8111730) baseStart_8111730 baseEnd_8111730 := by
    simpa [prefixWord, tailWord_8111730, baseEnd_8111730] using wordTrace_append hprefix tailTrace_8111730
  have hstable : (prefixWord ++ tailWord_8111730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111730).length < 2 ^ (prefixWord ++ tailWord_8111730).sum := by decide
  have hdescent : baseEnd_8111730 < baseStart_8111730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111737 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 1, 1, 3]
def baseStart_8111737 : Nat := 118140960795 + 8111737 * 2 ^ 59
def prefixEnd_8111737 : Nat := 4983230072969 + 3 ^ 40 * 8111737 * 2
def baseEnd_8111737 : Nat := 4165220023860234525382307

theorem tailTrace_8111737 : CollatzResearch.WordTrace tailWord_8111737 prefixEnd_8111737 4165220023860234525382307 := by
  unfold tailWord_8111737
  simp only [CollatzResearch.WordTrace]
  refine ⟨295859354213569698229421465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197239569475713132152947643 295859354213569698229421465)
  ·
    refine ⟨221894515660177273672066099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295859354213569698229421465 221894515660177273672066099)
    ·
      refine ⟨332841773490265910508099149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221894515660177273672066099 332841773490265910508099149)
      ·
        refine ⟨124815665058849716440537181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332841773490265910508099149 124815665058849716440537181)
        ·
          refine ⟨46805874397068643665201443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124815665058849716440537181 46805874397068643665201443)
          ·
            refine ⟨70208811595602965497802165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46805874397068643665201443 70208811595602965497802165)
            ·
              refine ⟨6582076087087778015418953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70208811595602965497802165 6582076087087778015418953)
              ·
                refine ⟨4936557065315833511564215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582076087087778015418953 4936557065315833511564215)
                ·
                  refine ⟨7404835597973750267346323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936557065315833511564215 7404835597973750267346323)
                  ·
                    refine ⟨11107253396960625401019485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7404835597973750267346323 11107253396960625401019485)
                    ·
                      refine ⟨4165220023860234525382307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107253396960625401019485 4165220023860234525382307)
                      ·
                        rfl

theorem cell23_8111737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_8111737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111737 prefixEnd_8111737 := by exact prefixLift 8111737
  have htrace : WordTrace (prefixWord ++ tailWord_8111737) baseStart_8111737 baseEnd_8111737 := by
    simpa [prefixWord, tailWord_8111737, baseEnd_8111737] using wordTrace_append hprefix tailTrace_8111737
  have hstable : (prefixWord ++ tailWord_8111737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111737).length < 2 ^ (prefixWord ++ tailWord_8111737).sum := by decide
  have hdescent : baseEnd_8111737 < baseStart_8111737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111739 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_8111739 : Nat := 118140960795 + 8111739 * 2 ^ 59
def prefixEnd_8111739 : Nat := 4983230072969 + 3 ^ 40 * 8111739 * 2
def baseEnd_8111739 : Nat := 4165221050821543517557297

theorem tailTrace_8111739 : CollatzResearch.WordTrace tailWord_8111739 prefixEnd_8111739 4165221050821543517557297 := by
  unfold tailWord_8111739
  simp only [CollatzResearch.WordTrace]
  refine ⟨295859427159562452570994271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197239618106374968380662847 295859427159562452570994271)
  ·
    refine ⟨443789140739343678856491407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295859427159562452570994271 443789140739343678856491407)
    ·
      refine ⟨665683711109015518284737111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443789140739343678856491407 665683711109015518284737111)
      ·
        refine ⟨998525566663523277427105667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665683711109015518284737111 998525566663523277427105667)
        ·
          refine ⟨1497788349995284916140658501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998525566663523277427105667 1497788349995284916140658501)
          ·
            refine ⟨280835315624115921776373469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1497788349995284916140658501 280835315624115921776373469)
            ·
              refine ⟨105313243359043470666140051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280835315624115921776373469 105313243359043470666140051)
              ·
                refine ⟨157969865038565205999210077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105313243359043470666140051 157969865038565205999210077)
                ·
                  refine ⟨59238699389461952249703779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157969865038565205999210077 59238699389461952249703779)
                  ·
                    refine ⟨88858049084192928374555669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59238699389461952249703779 88858049084192928374555669)
                    ·
                      refine ⟨4165221050821543517557297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88858049084192928374555669 4165221050821543517557297)
                      ·
                        rfl

theorem cell23_8111739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_8111739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111739 prefixEnd_8111739 := by exact prefixLift 8111739
  have htrace : WordTrace (prefixWord ++ tailWord_8111739) baseStart_8111739 baseEnd_8111739 := by
    simpa [prefixWord, tailWord_8111739, baseEnd_8111739] using wordTrace_append hprefix tailTrace_8111739
  have hstable : (prefixWord ++ tailWord_8111739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111739).length < 2 ^ (prefixWord ++ tailWord_8111739).sum := by decide
  have hdescent : baseEnd_8111739 < baseStart_8111739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111756 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_8111756 : Nat := 118140960795 + 8111756 * 2 ^ 59
def prefixEnd_8111756 : Nat := 4983230072969 + 3 ^ 40 * 8111756 * 2
def baseEnd_8111756 : Nat := 4165229779992669951044719

theorem tailTrace_8111756 : CollatzResearch.WordTrace tailWord_8111756 prefixEnd_8111756 4165229779992669951044719 := by
  unfold tailWord_8111756
  simp only [CollatzResearch.WordTrace]
  refine ⟨147930023600250432237181561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197240031467000576316242081 147930023600250432237181561)
  ·
    refine ⟨110947517700187824177886171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147930023600250432237181561 110947517700187824177886171)
    ·
      refine ⟨166421276550281736266829257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110947517700187824177886171 166421276550281736266829257)
      ·
        refine ⟨124815957412711302200121943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166421276550281736266829257 124815957412711302200121943)
        ·
          refine ⟨187223936119066953300182915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124815957412711302200121943 187223936119066953300182915)
          ·
            refine ⟨280835904178600429950274373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187223936119066953300182915 280835904178600429950274373)
            ·
              refine ⟨52656732033487580615676445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280835904178600429950274373 52656732033487580615676445)
              ·
                refine ⟨19746274512557842730878667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52656732033487580615676445 19746274512557842730878667)
                ·
                  refine ⟨29619411768836764096318001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19746274512557842730878667 29619411768836764096318001)
                  ·
                    refine ⟨22214558826627573072238501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29619411768836764096318001 22214558826627573072238501)
                    ·
                      refine ⟨4165229779992669951044719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22214558826627573072238501 4165229779992669951044719)
                      ·
                        rfl

theorem cell23_8111756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_8111756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111756 prefixEnd_8111756 := by exact prefixLift 8111756
  have htrace : WordTrace (prefixWord ++ tailWord_8111756) baseStart_8111756 baseEnd_8111756 := by
    simpa [prefixWord, tailWord_8111756, baseEnd_8111756] using wordTrace_append hprefix tailTrace_8111756
  have hstable : (prefixWord ++ tailWord_8111756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111756).length < 2 ^ (prefixWord ++ tailWord_8111756).sum := by decide
  have hdescent : baseEnd_8111756 < baseStart_8111756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111794 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_8111794 : Nat := 118140960795 + 8111794 * 2 ^ 59
def prefixEnd_8111794 : Nat := 4983230072969 + 3 ^ 40 * 8111794 * 2
def baseEnd_8111794 : Nat := 4165249292257540802369545

theorem tailTrace_8111794 : CollatzResearch.WordTrace tailWord_8111794 prefixEnd_8111794 4165249292257540802369545 := by
  unfold tailWord_8111794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73965358293590799241061609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197240955449575464642830957 73965358293590799241061609)
  ·
    refine ⟨55474018720193099430796207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73965358293590799241061609 55474018720193099430796207)
    ·
      refine ⟨83211028080289649146194311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55474018720193099430796207 83211028080289649146194311)
      ·
        refine ⟨124816542120434473719291467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83211028080289649146194311 124816542120434473719291467)
        ·
          refine ⟨187224813180651710578937201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124816542120434473719291467 187224813180651710578937201)
          ·
            refine ⟨140418609885488782934202901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187224813180651710578937201 140418609885488782934202901)
            ·
              refine ⟨6582122338382286700040761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140418609885488782934202901 6582122338382286700040761)
              ·
                refine ⟨4936591753786715025030571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582122338382286700040761 4936591753786715025030571)
                ·
                  refine ⟨7404887630680072537545857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936591753786715025030571 7404887630680072537545857)
                  ·
                    refine ⟨5553665723010054403159393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7404887630680072537545857 5553665723010054403159393)
                    ·
                      refine ⟨4165249292257540802369545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553665723010054403159393 4165249292257540802369545)
                      ·
                        rfl

theorem cell23_8111794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_8111794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111794 prefixEnd_8111794 := by exact prefixLift 8111794
  have htrace : WordTrace (prefixWord ++ tailWord_8111794) baseStart_8111794 baseEnd_8111794 := by
    simpa [prefixWord, tailWord_8111794, baseEnd_8111794] using wordTrace_append hprefix tailTrace_8111794
  have hstable : (prefixWord ++ tailWord_8111794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111794).length < 2 ^ (prefixWord ++ tailWord_8111794).sum := by decide
  have hdescent : baseEnd_8111794 < baseStart_8111794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111816 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_8111816 : Nat := 118140960795 + 8111816 * 2 ^ 59
def prefixEnd_8111816 : Nat := 4983230072969 + 3 ^ 40 * 8111816 * 2
def baseEnd_8111816 : Nat := 4165260588831939716294443

theorem tailTrace_8111816 : CollatzResearch.WordTrace tailWord_8111816 prefixEnd_8111816 4165260588831939716294443 := by
  unfold tailWord_8111816
  simp only [CollatzResearch.WordTrace]
  refine ⟨147931117790141747360773651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197241490386855663147698201 147931117790141747360773651)
  ·
    refine ⟨221896676685212621041160477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147931117790141747360773651 221896676685212621041160477)
    ·
      refine ⟨83211253756954732890435179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221896676685212621041160477 83211253756954732890435179)
      ·
        refine ⟨124816880635432099335652769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83211253756954732890435179 124816880635432099335652769)
        ·
          refine ⟨93612660476574074501739577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124816880635432099335652769 93612660476574074501739577)
          ·
            refine ⟨70209495357430555876304683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93612660476574074501739577 70209495357430555876304683)
            ·
              refine ⟨105314243036145833814457025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70209495357430555876304683 105314243036145833814457025)
              ·
                refine ⟨78985682277109375360842769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105314243036145833814457025 78985682277109375360842769)
                ·
                  refine ⟨59239261707832031520632077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78985682277109375360842769 59239261707832031520632077)
                  ·
                    refine ⟨22214723140437011820237029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59239261707832031520632077 22214723140437011820237029)
                    ·
                      refine ⟨4165260588831939716294443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22214723140437011820237029 4165260588831939716294443)
                      ·
                        rfl

theorem cell23_8111816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_8111816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111816 prefixEnd_8111816 := by exact prefixLift 8111816
  have htrace : WordTrace (prefixWord ++ tailWord_8111816) baseStart_8111816 baseEnd_8111816 := by
    simpa [prefixWord, tailWord_8111816, baseEnd_8111816] using wordTrace_append hprefix tailTrace_8111816
  have hstable : (prefixWord ++ tailWord_8111816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111816).length < 2 ^ (prefixWord ++ tailWord_8111816).sum := by decide
  have hdescent : baseEnd_8111816 < baseStart_8111816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111903 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 2, 5]
def baseStart_8111903 : Nat := 118140960795 + 8111903 * 2 ^ 59
def prefixEnd_8111903 : Nat := 4983230072969 + 3 ^ 40 * 8111903 * 2
def baseEnd_8111903 : Nat := 1388435087216293625302181

theorem tailTrace_8111903 : CollatzResearch.WordTrace tailWord_8111903 prefixEnd_8111903 1388435087216293625302181 := by
  unfold tailWord_8111903
  simp only [CollatzResearch.WordTrace]
  refine ⟨295865408730968308579964363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197243605820645539053309575 295865408730968308579964363)
  ·
    refine ⟨443798113096452462869946545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295865408730968308579964363 443798113096452462869946545)
    ·
      refine ⟨332848584822339347152459909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443798113096452462869946545 332848584822339347152459909)
      ·
        refine ⟨62409109654188627591086233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332848584822339347152459909 62409109654188627591086233)
        ·
          refine ⟨46806832240641470693314675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62409109654188627591086233 46806832240641470693314675)
          ·
            refine ⟨70210248360962206039972013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46806832240641470693314675 70210248360962206039972013)
            ·
              refine ⟨26328843135360827264989505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70210248360962206039972013 26328843135360827264989505)
              ·
                refine ⟨19746632351520620448742129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26328843135360827264989505 19746632351520620448742129)
                ·
                  refine ⟨14809974263640465336556597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19746632351520620448742129 14809974263640465336556597)
                  ·
                    refine ⟨1388435087216293625302181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14809974263640465336556597 1388435087216293625302181)
                    ·
                      rfl

theorem cell23_8111903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_8111903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111903 prefixEnd_8111903 := by exact prefixLift 8111903
  have htrace : WordTrace (prefixWord ++ tailWord_8111903) baseStart_8111903 baseEnd_8111903 := by
    simpa [prefixWord, tailWord_8111903, baseEnd_8111903] using wordTrace_append hprefix tailTrace_8111903
  have hstable : (prefixWord ++ tailWord_8111903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111903).length < 2 ^ (prefixWord ++ tailWord_8111903).sum := by decide
  have hdescent : baseEnd_8111903 < baseStart_8111903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111918 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_8111918 : Nat := 118140960795 + 8111918 * 2 ^ 59
def prefixEnd_8111918 : Nat := 4983230072969 + 3 ^ 40 * 8111918 * 2
def baseEnd_8111918 : Nat := 4165312963858698317218975

theorem tailTrace_8111918 : CollatzResearch.WordTrace tailWord_8111918 prefixEnd_8111918 4165312963858698317218975 := by
  unfold tailWord_8111918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983244478239245767720051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197243970550609310761173605 36983244478239245767720051)
  ·
    refine ⟨55474866717358868651580077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36983244478239245767720051 55474866717358868651580077)
    ·
      refine ⟨20803075019009575744342529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55474866717358868651580077 20803075019009575744342529)
      ·
        refine ⟨15602306264257181808256897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20803075019009575744342529 15602306264257181808256897)
        ·
          refine ⟨11701729698192886356192673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15602306264257181808256897 11701729698192886356192673)
          ·
            refine ⟨8776297273644664767144505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11701729698192886356192673 8776297273644664767144505)
            ·
              refine ⟨6582222955233498575358379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776297273644664767144505 6582222955233498575358379)
              ·
                refine ⟨9873334432850247863037569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582222955233498575358379 9873334432850247863037569)
                ·
                  refine ⟨7405000824637685897278177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9873334432850247863037569 7405000824637685897278177)
                  ·
                    refine ⟨5553750618478264422958633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7405000824637685897278177 5553750618478264422958633)
                    ·
                      refine ⟨4165312963858698317218975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553750618478264422958633 4165312963858698317218975)
                      ·
                        rfl

theorem cell23_8111918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_8111918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111918 prefixEnd_8111918 := by exact prefixLift 8111918
  have htrace : WordTrace (prefixWord ++ tailWord_8111918) baseStart_8111918 baseEnd_8111918 := by
    simpa [prefixWord, tailWord_8111918, baseEnd_8111918] using wordTrace_append hprefix tailTrace_8111918
  have hstable : (prefixWord ++ tailWord_8111918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111918).length < 2 ^ (prefixWord ++ tailWord_8111918).sum := by decide
  have hdescent : baseEnd_8111918 < baseStart_8111918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111936 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_8111936 : Nat := 118140960795 + 8111936 * 2 ^ 59
def prefixEnd_8111936 : Nat := 4983230072969 + 3 ^ 40 * 8111936 * 2
def baseEnd_8111936 : Nat := 4165322206510479246793891

theorem tailTrace_8111936 : CollatzResearch.WordTrace tailWord_8111936 prefixEnd_8111936 4165322206510479246793891 := by
  unfold tailWord_8111936
  simp only [CollatzResearch.WordTrace]
  refine ⟨147933306169924377607957831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197244408226565836810610441 147933306169924377607957831)
  ·
    refine ⟨221899959254886566411936747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147933306169924377607957831 221899959254886566411936747)
    ·
      refine ⟨332849938882329849617905121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221899959254886566411936747 332849938882329849617905121)
      ·
        refine ⟨249637454161747387213428841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332849938882329849617905121 249637454161747387213428841)
        ·
          refine ⟨187228090621310540410071631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249637454161747387213428841 187228090621310540410071631)
          ·
            refine ⟨280842135931965810615107447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187228090621310540410071631 280842135931965810615107447)
            ·
              refine ⟨421263203897948715922661171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280842135931965810615107447 421263203897948715922661171)
              ·
                refine ⟨631894805846923073883991757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421263203897948715922661171 631894805846923073883991757)
                ·
                  refine ⟨236960552192596152706496909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631894805846923073883991757 236960552192596152706496909)
                  ·
                    refine ⟨88860207072223557264936341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236960552192596152706496909 88860207072223557264936341)
                    ·
                      refine ⟨4165322206510479246793891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88860207072223557264936341 4165322206510479246793891)
                      ·
                        rfl

theorem cell23_8111936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_8111936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111936 prefixEnd_8111936 := by exact prefixLift 8111936
  have htrace : WordTrace (prefixWord ++ tailWord_8111936) baseStart_8111936 baseEnd_8111936 := by
    simpa [prefixWord, tailWord_8111936, baseEnd_8111936] using wordTrace_append hprefix tailTrace_8111936
  have hstable : (prefixWord ++ tailWord_8111936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111936).length < 2 ^ (prefixWord ++ tailWord_8111936).sum := by decide
  have hdescent : baseEnd_8111936 < baseStart_8111936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111943 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_8111943 : Nat := 118140960795 + 8111943 * 2 ^ 59
def prefixEnd_8111943 : Nat := 4983230072969 + 3 ^ 40 * 8111943 * 2
def baseEnd_8111943 : Nat := 4165325800875060719406359

theorem tailTrace_8111943 : CollatzResearch.WordTrace tailWord_8111943 prefixEnd_8111943 4165325800875060719406359 := by
  unfold tailWord_8111943
  simp only [CollatzResearch.WordTrace]
  refine ⟨295866867650823395411420483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197244578433882263607613655 295866867650823395411420483)
  ·
    refine ⟨443800301476235093117130725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295866867650823395411420483 443800301476235093117130725)
    ·
      refine ⟨83212556526794079959462011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443800301476235093117130725 83212556526794079959462011)
      ·
        refine ⟨124818834790191119939193017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83212556526794079959462011 124818834790191119939193017)
        ·
          refine ⟨93614126092643339954394763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124818834790191119939193017 93614126092643339954394763)
          ·
            refine ⟨140421189138965009931592145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93614126092643339954394763 140421189138965009931592145)
            ·
              refine ⟨105315891854223757448694109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140421189138965009931592145 105315891854223757448694109)
              ·
                refine ⟨39493459445333909043260291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105315891854223757448694109 39493459445333909043260291)
                ·
                  refine ⟨59240189168000863564890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39493459445333909043260291 59240189168000863564890437)
                  ·
                    refine ⟨11107535469000161918416957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59240189168000863564890437 11107535469000161918416957)
                    ·
                      refine ⟨4165325800875060719406359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107535469000161918416957 4165325800875060719406359)
                      ·
                        rfl

theorem cell23_8111943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_8111943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111943 prefixEnd_8111943 := by exact prefixLift 8111943
  have htrace : WordTrace (prefixWord ++ tailWord_8111943) baseStart_8111943 baseEnd_8111943 := by
    simpa [prefixWord, tailWord_8111943, baseEnd_8111943] using wordTrace_append hprefix tailTrace_8111943
  have hstable : (prefixWord ++ tailWord_8111943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111943).length < 2 ^ (prefixWord ++ tailWord_8111943).sum := by decide
  have hdescent : baseEnd_8111943 < baseStart_8111943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111967 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 1, 4]
def baseStart_8111967 : Nat := 118140960795 + 8111967 * 2 ^ 59
def prefixEnd_8111967 : Nat := 4983230072969 + 3 ^ 40 * 8111967 * 2
def baseEnd_8111967 : Nat := 1388446041470256208502083

theorem tailTrace_8111967 : CollatzResearch.WordTrace tailWord_8111967 prefixEnd_8111967 1388446041470256208502083 := by
  unfold tailWord_8111967
  simp only [CollatzResearch.WordTrace]
  refine ⟨295867743002736447510294155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197245162001824298340196103 295867743002736447510294155)
  ·
    refine ⟨443801614504104671265441233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295867743002736447510294155 443801614504104671265441233)
    ·
      refine ⟨332851210878078503449080925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443801614504104671265441233 332851210878078503449080925)
      ·
        refine ⟨124819204079279438793405347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332851210878078503449080925 124819204079279438793405347)
        ·
          refine ⟨187228806118919158190108021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124819204079279438793405347 187228806118919158190108021)
          ·
            refine ⟨17552700573648671080322627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187228806118919158190108021 17552700573648671080322627)
            ·
              refine ⟨26329050860473006620483941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552700573648671080322627 26329050860473006620483941)
              ·
                refine ⟨4936697036338688741340739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26329050860473006620483941 4936697036338688741340739)
                ·
                  refine ⟨7405045554508033112011109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936697036338688741340739 7405045554508033112011109)
                  ·
                    refine ⟨1388446041470256208502083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405045554508033112011109 1388446041470256208502083)
                    ·
                      rfl

theorem cell23_8111967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 4].length) (baseStart_8111967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111967 prefixEnd_8111967 := by exact prefixLift 8111967
  have htrace : WordTrace (prefixWord ++ tailWord_8111967) baseStart_8111967 baseEnd_8111967 := by
    simpa [prefixWord, tailWord_8111967, baseEnd_8111967] using wordTrace_append hprefix tailTrace_8111967
  have hstable : (prefixWord ++ tailWord_8111967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111967).length < 2 ^ (prefixWord ++ tailWord_8111967).sum := by decide
  have hdescent : baseEnd_8111967 < baseStart_8111967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111973 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_8111973 : Nat := 118140960795 + 8111973 * 2 ^ 59
def prefixEnd_8111973 : Nat := 4983230072969 + 3 ^ 40 * 8111973 * 2
def baseEnd_8111973 : Nat := 4165341205294695602031221

theorem tailTrace_8111973 : CollatzResearch.WordTrace tailWord_8111973 prefixEnd_8111973 4165341205294695602031221 := by
  unfold tailWord_8111973
  simp only [CollatzResearch.WordTrace]
  refine ⟨295867961840714710535012573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197245307893809807023341715 295867961840714710535012573)
  ·
    refine ⟨110950485690268016450629715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295867961840714710535012573 110950485690268016450629715)
    ·
      refine ⟨166425728535402024675944573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110950485690268016450629715 166425728535402024675944573)
      ·
        refine ⟨62409648200775759253479215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166425728535402024675944573 62409648200775759253479215)
        ·
          refine ⟨93614472301163638880218823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62409648200775759253479215 93614472301163638880218823)
          ·
            refine ⟨140421708451745458320328235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93614472301163638880218823 140421708451745458320328235)
            ·
              refine ⟨210632562677618187480492353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140421708451745458320328235 210632562677618187480492353)
              ·
                refine ⟨157974422008213640610369265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210632562677618187480492353 157974422008213640610369265)
                ·
                  refine ⟨118480816506160230457776949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157974422008213640610369265 118480816506160230457776949)
                  ·
                    refine ⟨11107576547452521605416589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118480816506160230457776949 11107576547452521605416589)
                    ·
                      refine ⟨4165341205294695602031221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107576547452521605416589 4165341205294695602031221)
                      ·
                        rfl

theorem cell23_8111973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_8111973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111973 prefixEnd_8111973 := by exact prefixLift 8111973
  have htrace : WordTrace (prefixWord ++ tailWord_8111973) baseStart_8111973 baseEnd_8111973 := by
    simpa [prefixWord, tailWord_8111973, baseEnd_8111973] using wordTrace_append hprefix tailTrace_8111973
  have hstable : (prefixWord ++ tailWord_8111973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111973).length < 2 ^ (prefixWord ++ tailWord_8111973).sum := by decide
  have hdescent : baseEnd_8111973 < baseStart_8111973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8111993 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_8111993 : Nat := 118140960795 + 8111993 * 2 ^ 59
def prefixEnd_8111993 : Nat := 4983230072969 + 3 ^ 40 * 8111993 * 2
def baseEnd_8111993 : Nat := 1388450491635928507927043

theorem tailTrace_8111993 : CollatzResearch.WordTrace tailWord_8111993 prefixEnd_8111993 1388450491635928507927043 := by
  unfold tailWord_8111993
  simp only [CollatzResearch.WordTrace]
  refine ⟨295868691300642253950740633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197245794200428169300493755 295868691300642253950740633)
  ·
    refine ⟨221901518475481690463055475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295868691300642253950740633 221901518475481690463055475)
    ·
      refine ⟨332852277713222535694583213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221901518475481690463055475 332852277713222535694583213)
      ·
        refine ⟨124819604142458450885468705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332852277713222535694583213 124819604142458450885468705)
        ·
          refine ⟨93614703106843838164101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124819604142458450885468705 93614703106843838164101529)
          ·
            refine ⟨70211027330132878623076147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93614703106843838164101529 70211027330132878623076147)
            ·
              refine ⟨105316540995199317934614221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70211027330132878623076147 105316540995199317934614221)
              ·
                refine ⟨39493702873199744225480333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105316540995199317934614221 39493702873199744225480333)
                ·
                  refine ⟨14810138577449904084555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39493702873199744225480333 14810138577449904084555125)
                  ·
                    refine ⟨1388450491635928507927043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14810138577449904084555125 1388450491635928507927043)
                    ·
                      rfl

theorem cell23_8111993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_8111993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8111993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8111993 prefixEnd_8111993 := by exact prefixLift 8111993
  have htrace : WordTrace (prefixWord ++ tailWord_8111993) baseStart_8111993 baseEnd_8111993 := by
    simpa [prefixWord, tailWord_8111993, baseEnd_8111993] using wordTrace_append hprefix tailTrace_8111993
  have hstable : (prefixWord ++ tailWord_8111993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8111993).length < 2 ^ (prefixWord ++ tailWord_8111993).sum := by decide
  have hdescent : baseEnd_8111993 < baseStart_8111993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8111993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112000 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2]
def baseStart_8112000 : Nat := 118140960795 + 8112000 * 2 ^ 59
def prefixEnd_8112000 : Nat := 4983230072969 + 3 ^ 40 * 8112000 * 2
def baseEnd_8112000 : Nat := 4165355069272366996393597

theorem tailTrace_8112000 : CollatzResearch.WordTrace tailWord_8112000 prefixEnd_8112000 4165355069272366996393597 := by
  unfold tailWord_8112000
  simp only [CollatzResearch.WordTrace]
  refine ⟨147934473305808447073122727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197245964407744596097496969 147934473305808447073122727)
  ·
    refine ⟨221901709958712670609684091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147934473305808447073122727 221901709958712670609684091)
    ·
      refine ⟨332852564938069005914526137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221901709958712670609684091 332852564938069005914526137)
      ·
        refine ⟨249639423703551754435894603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332852564938069005914526137 249639423703551754435894603)
        ·
          refine ⟨374459135555327631653841905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249639423703551754435894603 374459135555327631653841905)
          ·
            refine ⟨280844351666495723740381429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374459135555327631653841905 280844351666495723740381429)
            ·
              refine ⟨26329157968733974100660759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280844351666495723740381429 26329157968733974100660759)
              ·
                refine ⟨39493736953100961150991139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26329157968733974100660759 39493736953100961150991139)
                ·
                  refine ⟨59240605429651441726486709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39493736953100961150991139 59240605429651441726486709)
                  ·
                    refine ⟨5553806759029822661858129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59240605429651441726486709 5553806759029822661858129)
                    ·
                      refine ⟨4165355069272366996393597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553806759029822661858129 4165355069272366996393597)
                      ·
                        rfl

theorem cell23_8112000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_8112000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112000 prefixEnd_8112000 := by exact prefixLift 8112000
  have htrace : WordTrace (prefixWord ++ tailWord_8112000) baseStart_8112000 baseEnd_8112000 := by
    simpa [prefixWord, tailWord_8112000, baseEnd_8112000] using wordTrace_append hprefix tailTrace_8112000
  have hstable : (prefixWord ++ tailWord_8112000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112000).length < 2 ^ (prefixWord ++ tailWord_8112000).sum := by decide
  have hdescent : baseEnd_8112000 < baseStart_8112000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112001 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 1, 4]
def baseStart_8112001 : Nat := 118140960795 + 8112001 * 2 ^ 59
def prefixEnd_8112001 : Nat := 4983230072969 + 3 ^ 40 * 8112001 * 2
def baseEnd_8112001 : Nat := 1388451860917673830827031

theorem tailTrace_8112001 : CollatzResearch.WordTrace tailWord_8112001 prefixEnd_8112001 1388451860917673830827031 := by
  unfold tailWord_8112001
  simp only [CollatzResearch.WordTrace]
  refine ⟨295868983084613271317031857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197245988723075514211354571 295868983084613271317031857)
  ·
    refine ⟨221901737313459953487773893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295868983084613271317031857 221901737313459953487773893)
    ·
      refine ⟨41606575746273741278957605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221901737313459953487773893 41606575746273741278957605)
      ·
        refine ⟨7801232952426326489804551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41606575746273741278957605 7801232952426326489804551)
        ·
          refine ⟨11701849428639489734706827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801232952426326489804551 11701849428639489734706827)
          ·
            refine ⟨17552774142959234602060241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701849428639489734706827 17552774142959234602060241)
            ·
              refine ⟨13164580607219425951545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17552774142959234602060241 13164580607219425951545181)
              ·
                refine ⟨4936717727707284731829443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13164580607219425951545181 4936717727707284731829443)
                ·
                  refine ⟨7405076591560927097744165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936717727707284731829443 7405076591560927097744165)
                  ·
                    refine ⟨1388451860917673830827031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405076591560927097744165 1388451860917673830827031)
                    ·
                      rfl

theorem cell23_8112001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_8112001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112001 prefixEnd_8112001 := by exact prefixLift 8112001
  have htrace : WordTrace (prefixWord ++ tailWord_8112001) baseStart_8112001 baseEnd_8112001 := by
    simpa [prefixWord, tailWord_8112001, baseEnd_8112001] using wordTrace_append hprefix tailTrace_8112001
  have hstable : (prefixWord ++ tailWord_8112001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112001).length < 2 ^ (prefixWord ++ tailWord_8112001).sum := by decide
  have hdescent : baseEnd_8112001 < baseStart_8112001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112014 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_8112014 : Nat := 118140960795 + 8112014 * 2 ^ 59
def prefixEnd_8112014 : Nat := 4983230072969 + 3 ^ 40 * 8112014 * 2
def baseEnd_8112014 : Nat := 462818028666836660179837

theorem tailTrace_8112014 : CollatzResearch.WordTrace tailWord_8112014 prefixEnd_8112014 462818028666836660179837 := by
  unfold tailWord_8112014
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983682154195771817156887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197246304822377449691503397 36983682154195771817156887)
  ·
    refine ⟨55475523231293657725735331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36983682154195771817156887 55475523231293657725735331)
    ·
      refine ⟨83213284846940486588602997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55475523231293657725735331 83213284846940486588602997)
      ·
        refine ⟨7801245454400670617681531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83213284846940486588602997 7801245454400670617681531)
        ·
          refine ⟨11701868181601005926522297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801245454400670617681531 11701868181601005926522297)
          ·
            refine ⟨8776401136200754444891723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11701868181601005926522297 8776401136200754444891723)
            ·
              refine ⟨13164601704301131667337585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776401136200754444891723 13164601704301131667337585)
              ·
                refine ⟨9873451278225848750503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13164601704301131667337585 9873451278225848750503189)
                ·
                  refine ⟨462818028666836660179837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9873451278225848750503189 462818028666836660179837)
                  ·
                    rfl

theorem cell23_8112014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_8112014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112014 prefixEnd_8112014 := by exact prefixLift 8112014
  have htrace : WordTrace (prefixWord ++ tailWord_8112014) baseStart_8112014 baseEnd_8112014 := by
    simpa [prefixWord, tailWord_8112014, baseEnd_8112014] using wordTrace_append hprefix tailTrace_8112014
  have hstable : (prefixWord ++ tailWord_8112014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112014).length < 2 ^ (prefixWord ++ tailWord_8112014).sum := by decide
  have hdescent : baseEnd_8112014 < baseStart_8112014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112047 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 3, 2, 2]
def baseStart_8112047 : Nat := 118140960795 + 8112047 * 2 ^ 59
def prefixEnd_8112047 : Nat := 4983230072969 + 3 ^ 40 * 8112047 * 2
def baseEnd_8112047 : Nat := 4165379202863128312505881

theorem tailTrace_8112047 : CollatzResearch.WordTrace tailWord_8112047 prefixEnd_8112047 4165379202863128312505881 := by
  unfold tailWord_8112047
  simp only [CollatzResearch.WordTrace]
  refine ⟨295870660842446621173206395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197247107228297747448804263 295870660842446621173206395)
  ·
    refine ⟨443805991263669931759809593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295870660842446621173206395 443805991263669931759809593)
    ·
      refine ⟨332854493447752448819857195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443805991263669931759809593 332854493447752448819857195)
      ·
        refine ⟨499281740171628673229785793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332854493447752448819857195 499281740171628673229785793)
        ·
          refine ⟨374461305128721504922339345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499281740171628673229785793 374461305128721504922339345)
          ·
            refine ⟨280845978846541128691754509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374461305128721504922339345 280845978846541128691754509)
            ·
              refine ⟨105317242067452923259407941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280845978846541128691754509 105317242067452923259407941)
              ·
                refine ⟨19746982887647423111138989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105317242067452923259407941 19746982887647423111138989)
                ·
                  refine ⟨7405118582867783666677121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19746982887647423111138989 7405118582867783666677121)
                  ·
                    refine ⟨5553838937150837750007841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7405118582867783666677121 5553838937150837750007841)
                    ·
                      refine ⟨4165379202863128312505881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553838937150837750007841 4165379202863128312505881)
                      ·
                        rfl

theorem cell23_8112047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 2, 2].length) (baseStart_8112047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112047 prefixEnd_8112047 := by exact prefixLift 8112047
  have htrace : WordTrace (prefixWord ++ tailWord_8112047) baseStart_8112047 baseEnd_8112047 := by
    simpa [prefixWord, tailWord_8112047, baseEnd_8112047] using wordTrace_append hprefix tailTrace_8112047
  have hstable : (prefixWord ++ tailWord_8112047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112047).length < 2 ^ (prefixWord ++ tailWord_8112047).sum := by decide
  have hdescent : baseEnd_8112047 < baseStart_8112047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112050 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_8112050 : Nat := 118140960795 + 8112050 * 2 ^ 59
def prefixEnd_8112050 : Nat := 4983230072969 + 3 ^ 40 * 8112050 * 2
def baseEnd_8112050 : Nat := 4165380743305091800768367

theorem tailTrace_8112050 : CollatzResearch.WordTrace tailWord_8112050 prefixEnd_8112050 4165380743305091800768367 := by
  unfold tailWord_8112050
  simp only [CollatzResearch.WordTrace]
  refine ⟨73967692565358938171391401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197247180174290501790377069 73967692565358938171391401)
  ·
    refine ⟨55475769424019203628543551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73967692565358938171391401 55475769424019203628543551)
    ·
      refine ⟨83213654136028805442815327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55475769424019203628543551 83213654136028805442815327)
      ·
        refine ⟨124820481204043208164222991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83213654136028805442815327 124820481204043208164222991)
        ·
          refine ⟨187230721806064812246334487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124820481204043208164222991 187230721806064812246334487)
          ·
            refine ⟨280846082709097218369501731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187230721806064812246334487 280846082709097218369501731)
            ·
              refine ⟨421269124063645827554252597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280846082709097218369501731 421269124063645827554252597)
              ·
                refine ⟨39493980380966796333211181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421269124063645827554252597 39493980380966796333211181)
                ·
                  refine ⟨14810242642862548624954193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39493980380966796333211181 14810242642862548624954193)
                  ·
                    refine ⟨11107681982146911468715645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14810242642862548624954193 11107681982146911468715645)
                    ·
                      refine ⟨4165380743305091800768367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107681982146911468715645 4165380743305091800768367)
                      ·
                        rfl

theorem cell23_8112050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_8112050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112050 prefixEnd_8112050 := by exact prefixLift 8112050
  have htrace : WordTrace (prefixWord ++ tailWord_8112050) baseStart_8112050 baseEnd_8112050 := by
    simpa [prefixWord, tailWord_8112050, baseEnd_8112050] using wordTrace_append hprefix tailTrace_8112050
  have hstable : (prefixWord ++ tailWord_8112050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112050).length < 2 ^ (prefixWord ++ tailWord_8112050).sum := by decide
  have hdescent : baseEnd_8112050 < baseStart_8112050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112098 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_8112098 : Nat := 118140960795 + 8112098 * 2 ^ 59
def prefixEnd_8112098 : Nat := 4983230072969 + 3 ^ 40 * 8112098 * 2
def baseEnd_8112098 : Nat := 4165405390376507612968147

theorem tailTrace_8112098 : CollatzResearch.WordTrace tailWord_8112098 prefixEnd_8112098 4165405390376507612968147 := by
  unfold tailWord_8112098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73968130241315464220828237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197248347310174571255541965 73968130241315464220828237)
  ·
    refine ⟨27738048840493299082810589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73968130241315464220828237 27738048840493299082810589)
    ·
      refine ⟨10401768315184987156053971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27738048840493299082810589 10401768315184987156053971)
      ·
        refine ⟨15602652472777480734080957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10401768315184987156053971 15602652472777480734080957)
        ·
          refine ⟨5850994677291555275280359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15602652472777480734080957 5850994677291555275280359)
          ·
            refine ⟨8776492015937332912920539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850994677291555275280359 8776492015937332912920539)
            ·
              refine ⟨13164738023905999369380809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776492015937332912920539 13164738023905999369380809)
              ·
                refine ⟨9873553517929499527035607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13164738023905999369380809 9873553517929499527035607)
                ·
                  refine ⟨14810330276894249290553411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873553517929499527035607 14810330276894249290553411)
                  ·
                    refine ⟨22215495415341373935830117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14810330276894249290553411 22215495415341373935830117)
                    ·
                      refine ⟨4165405390376507612968147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22215495415341373935830117 4165405390376507612968147)
                      ·
                        rfl

theorem cell23_8112098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_8112098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112098 prefixEnd_8112098 := by exact prefixLift 8112098
  have htrace : WordTrace (prefixWord ++ tailWord_8112098) baseStart_8112098 baseEnd_8112098 := by
    simpa [prefixWord, tailWord_8112098, baseEnd_8112098] using wordTrace_append hprefix tailTrace_8112098
  have hstable : (prefixWord ++ tailWord_8112098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112098).length < 2 ^ (prefixWord ++ tailWord_8112098).sum := by decide
  have hdescent : baseEnd_8112098 < baseStart_8112098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112132 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8112132 : Nat := 118140960795 + 8112132 * 2 ^ 59
def prefixEnd_8112132 : Nat := 4983230072969 + 3 ^ 40 * 8112132 * 2
def baseEnd_8112132 : Nat := 4165422848718760479942991

theorem tailTrace_8112132 : CollatzResearch.WordTrace tailWord_8112132 prefixEnd_8112132 4165422848718760479942991 := by
  unfold tailWord_8112132
  simp only [CollatzResearch.WordTrace]
  refine ⟨147936880523569340345025325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197249174031425787126700433 147936880523569340345025325)
  ·
    refine ⟨55476330196338502629384497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147936880523569340345025325 55476330196338502629384497)
    ·
      refine ⟨41607247647253876972038373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55476330196338502629384497 41607247647253876972038373)
      ·
        refine ⟨7801358933860101932257195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41607247647253876972038373 7801358933860101932257195)
        ·
          refine ⟨11702038400790152898385793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801358933860101932257195 11702038400790152898385793)
          ·
            refine ⟨8776528800592614673789345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702038400790152898385793 8776528800592614673789345)
            ·
              refine ⟨6582396600444461005342009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776528800592614673789345 6582396600444461005342009)
              ·
                refine ⟨4936797450333345754006507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582396600444461005342009 4936797450333345754006507)
                ·
                  refine ⟨7405196175500018631009761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936797450333345754006507 7405196175500018631009761)
                  ·
                    refine ⟨5553897131625013973257321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7405196175500018631009761 5553897131625013973257321)
                    ·
                      refine ⟨4165422848718760479942991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553897131625013973257321 4165422848718760479942991)
                      ·
                        rfl

theorem cell23_8112132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8112132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112132 prefixEnd_8112132 := by exact prefixLift 8112132
  have htrace : WordTrace (prefixWord ++ tailWord_8112132) baseStart_8112132 baseEnd_8112132 := by
    simpa [prefixWord, tailWord_8112132, baseEnd_8112132] using wordTrace_append hprefix tailTrace_8112132
  have hstable : (prefixWord ++ tailWord_8112132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112132).length < 2 ^ (prefixWord ++ tailWord_8112132).sum := by decide
  have hdescent : baseEnd_8112132 < baseStart_8112132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112140 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_8112140 : Nat := 118140960795 + 8112140 * 2 ^ 59
def prefixEnd_8112140 : Nat := 4983230072969 + 3 ^ 40 * 8112140 * 2
def baseEnd_8112140 : Nat := 4165426956563996448642953

theorem tailTrace_8112140 : CollatzResearch.WordTrace tailWord_8112140 prefixEnd_8112140 4165426956563996448642953 := by
  unfold tailWord_8112140
  simp only [CollatzResearch.WordTrace]
  refine ⟨147937026415554849028170937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197249368554073132037561249 147937026415554849028170937)
  ·
    refine ⟨110952769811666136771128203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147937026415554849028170937 110952769811666136771128203)
    ·
      refine ⟨166429154717499205156692305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110952769811666136771128203 166429154717499205156692305)
      ·
        refine ⟨124821866038124403867519229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166429154717499205156692305 124821866038124403867519229)
        ·
          refine ⟨46808199764296651450319711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124821866038124403867519229 46808199764296651450319711)
          ·
            refine ⟨70212299646444977175479567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46808199764296651450319711 70212299646444977175479567)
            ·
              refine ⟨105318449469667465763219351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70212299646444977175479567 105318449469667465763219351)
              ·
                refine ⟨157977674204501198644829027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105318449469667465763219351 157977674204501198644829027)
                ·
                  refine ⟨236966511306751797967243541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157977674204501198644829027 236966511306751797967243541)
                  ·
                    refine ⟨11107805217503990529714541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 236966511306751797967243541 11107805217503990529714541)
                    ·
                      refine ⟨4165426956563996448642953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107805217503990529714541 4165426956563996448642953)
                      ·
                        rfl

theorem cell23_8112140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_8112140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112140 prefixEnd_8112140 := by exact prefixLift 8112140
  have htrace : WordTrace (prefixWord ++ tailWord_8112140) baseStart_8112140 baseEnd_8112140 := by
    simpa [prefixWord, tailWord_8112140, baseEnd_8112140] using wordTrace_append hprefix tailTrace_8112140
  have hstable : (prefixWord ++ tailWord_8112140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112140).length < 2 ^ (prefixWord ++ tailWord_8112140).sum := by decide
  have hdescent : baseEnd_8112140 < baseStart_8112140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112154 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_8112154 : Nat := 118140960795 + 8112154 * 2 ^ 59
def prefixEnd_8112154 : Nat := 4983230072969 + 3 ^ 40 * 8112154 * 2
def baseEnd_8112154 : Nat := 4165434145293159393867889

theorem tailTrace_8112154 : CollatzResearch.WordTrace tailWord_8112154 prefixEnd_8112154 4165434145293159393867889 := by
  unfold tailWord_8112154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73968640863264744611837879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197249708968705985631567677 73968640863264744611837879)
  ·
    refine ⟨110952961294897116917756819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73968640863264744611837879 110952961294897116917756819)
    ·
      refine ⟨166429441942345675376635229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110952961294897116917756819 166429441942345675376635229)
      ·
        refine ⟨62411040728379628266238211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166429441942345675376635229 62411040728379628266238211)
        ·
          refine ⟨93616561092569442399357317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62411040728379628266238211 93616561092569442399357317)
          ·
            refine ⟨17553105204856770449879497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93616561092569442399357317 17553105204856770449879497)
            ·
              refine ⟨13164828903642577837409623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17553105204856770449879497 13164828903642577837409623)
              ·
                refine ⟨19747243355463866756114435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13164828903642577837409623 19747243355463866756114435)
                ·
                  refine ⟨29620865033195800134171653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19747243355463866756114435 29620865033195800134171653)
                  ·
                    refine ⟨5553912193724212525157185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29620865033195800134171653 5553912193724212525157185)
                    ·
                      refine ⟨4165434145293159393867889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553912193724212525157185 4165434145293159393867889)
                      ·
                        rfl

theorem cell23_8112154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_8112154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112154 prefixEnd_8112154 := by exact prefixLift 8112154
  have htrace : WordTrace (prefixWord ++ tailWord_8112154) baseStart_8112154 baseEnd_8112154 := by
    simpa [prefixWord, tailWord_8112154, baseEnd_8112154] using wordTrace_append hprefix tailTrace_8112154
  have hstable : (prefixWord ++ tailWord_8112154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112154).length < 2 ^ (prefixWord ++ tailWord_8112154).sum := by decide
  have hdescent : baseEnd_8112154 < baseStart_8112154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112177 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 5]
def baseStart_8112177 : Nat := 118140960795 + 8112177 * 2 ^ 59
def prefixEnd_8112177 : Nat := 4983230072969 + 3 ^ 40 * 8112177 * 2
def baseEnd_8112177 : Nat := 462827328372023644875587

theorem tailTrace_8112177 : CollatzResearch.WordTrace tailWord_8112177 prefixEnd_8112177 462827328372023644875587 := by
  unfold tailWord_8112177
  simp only [CollatzResearch.WordTrace]
  refine ⟨295875402331975653375438785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197250268221317102250292523 295875402331975653375438785)
  ·
    refine ⟨221906551748981740031579089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295875402331975653375438785 221906551748981740031579089)
    ·
      refine ⟨166429913811736305023684317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221906551748981740031579089 166429913811736305023684317)
      ·
        refine ⟨62411217679401114383881619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166429913811736305023684317 62411217679401114383881619)
        ·
          refine ⟨93616826519101671575822429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62411217679401114383881619 93616826519101671575822429)
          ·
            refine ⟨35106309944663126840933411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93616826519101671575822429 35106309944663126840933411)
            ·
              refine ⟨52659464916994690261400117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35106309944663126840933411 52659464916994690261400117)
              ·
                refine ⟨4936824835968252212006261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52659464916994690261400117 4936824835968252212006261)
                ·
                  refine ⟨462827328372023644875587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936824835968252212006261 462827328372023644875587)
                  ·
                    rfl

theorem cell23_8112177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 5].length) (baseStart_8112177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112177 prefixEnd_8112177 := by exact prefixLift 8112177
  have htrace : WordTrace (prefixWord ++ tailWord_8112177) baseStart_8112177 baseEnd_8112177 := by
    simpa [prefixWord, tailWord_8112177, baseEnd_8112177] using wordTrace_append hprefix tailTrace_8112177
  have hstable : (prefixWord ++ tailWord_8112177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112177).length < 2 ^ (prefixWord ++ tailWord_8112177).sum := by decide
  have hdescent : baseEnd_8112177 < baseStart_8112177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112227 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 6, 2]
def baseStart_8112227 : Nat := 118140960795 + 8112227 * 2 ^ 59
def prefixEnd_8112227 : Nat := 4983230072969 + 3 ^ 40 * 8112227 * 2
def baseEnd_8112227 : Nat := 4165471629380937608255053

theorem tailTrace_8112227 : CollatzResearch.WordTrace tailWord_8112227 prefixEnd_8112227 4165471629380937608255053 := by
  unfold tailWord_8112227
  simp only [CollatzResearch.WordTrace]
  refine ⟨295877225981794511914758935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197251483987863007943172623 295877225981794511914758935)
  ·
    refine ⟨443815838972691767872138403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295877225981794511914758935 443815838972691767872138403)
    ·
      refine ⟨665723758459037651808207605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443815838972691767872138403 665723758459037651808207605)
      ·
        refine ⟨62411602355534779857019463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 665723758459037651808207605 62411602355534779857019463)
        ·
          refine ⟨93617403533302169785529195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62411602355534779857019463 93617403533302169785529195)
          ·
            refine ⟨140426105299953254678293793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93617403533302169785529195 140426105299953254678293793)
            ·
              refine ⟨105319578974964941008720345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140426105299953254678293793 105319578974964941008720345)
              ·
                refine ⟨78989684231223705756540259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105319578974964941008720345 78989684231223705756540259)
                ·
                  refine ⟨118484526346835558634810389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78989684231223705756540259 118484526346835558634810389)
                  ·
                    refine ⟨5553962172507916811006737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118484526346835558634810389 5553962172507916811006737)
                    ·
                      refine ⟨4165471629380937608255053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5553962172507916811006737 4165471629380937608255053)
                      ·
                        rfl

theorem cell23_8112227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_8112227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112227 prefixEnd_8112227 := by exact prefixLift 8112227
  have htrace : WordTrace (prefixWord ++ tailWord_8112227) baseStart_8112227 baseEnd_8112227 := by
    simpa [prefixWord, tailWord_8112227, baseEnd_8112227] using wordTrace_append hprefix tailTrace_8112227
  have hstable : (prefixWord ++ tailWord_8112227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112227).length < 2 ^ (prefixWord ++ tailWord_8112227).sum := by decide
  have hdescent : baseEnd_8112227 < baseStart_8112227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112247 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_8112247 : Nat := 118140960795 + 8112247 * 2 ^ 59
def prefixEnd_8112247 : Nat := 4983230072969 + 3 ^ 40 * 8112247 * 2
def baseEnd_8112247 : Nat := 4165481898994027530004961

theorem tailTrace_8112247 : CollatzResearch.WordTrace tailWord_8112247 prefixEnd_8112247 4165481898994027530004961 := by
  unfold tailWord_8112247
  simp only [CollatzResearch.WordTrace]
  refine ⟨295877955441722055330486995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197251970294481370220324663 295877955441722055330486995)
  ·
    refine ⟨443816933162583082995730493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295877955441722055330486995 443816933162583082995730493)
    ·
      refine ⟨166431349935968656123398935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443816933162583082995730493 166431349935968656123398935)
      ·
        refine ⟨249647024903952984185098403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166431349935968656123398935 249647024903952984185098403)
        ·
          refine ⟨374470537355929476277647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249647024903952984185098403 374470537355929476277647605)
          ·
            refine ⟨35106612877118388401029463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374470537355929476277647605 35106612877118388401029463)
            ·
              refine ⟨52659919315677582601544195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35106612877118388401029463 52659919315677582601544195)
              ·
                refine ⟨78989878973516373902316293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52659919315677582601544195 78989878973516373902316293)
                ·
                  refine ⟨14810602307534320106684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78989878973516373902316293 14810602307534320106684305)
                  ·
                    refine ⟨11107951730650740080013229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14810602307534320106684305 11107951730650740080013229)
                    ·
                      refine ⟨4165481898994027530004961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11107951730650740080013229 4165481898994027530004961)
                      ·
                        rfl

theorem cell23_8112247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_8112247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112247 prefixEnd_8112247 := by exact prefixLift 8112247
  have htrace : WordTrace (prefixWord ++ tailWord_8112247) baseStart_8112247 baseEnd_8112247 := by
    simpa [prefixWord, tailWord_8112247, baseEnd_8112247] using wordTrace_append hprefix tailTrace_8112247
  have hstable : (prefixWord ++ tailWord_8112247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112247).length < 2 ^ (prefixWord ++ tailWord_8112247).sum := by decide
  have hdescent : baseEnd_8112247 < baseStart_8112247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112305 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 1, 4]
def baseStart_8112305 : Nat := 118140960795 + 8112305 * 2 ^ 59
def prefixEnd_8112305 : Nat := 4983230072969 + 3 ^ 40 * 8112305 * 2
def baseEnd_8112305 : Nat := 1388503893623996101026565

theorem tailTrace_8112305 : CollatzResearch.WordTrace tailWord_8112305 prefixEnd_8112305 1388503893623996101026565 := by
  unfold tailWord_8112305
  simp only [CollatzResearch.WordTrace]
  refine ⟨295880070875511931236098369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197253380583674620824065579 295880070875511931236098369)
  ·
    refine ⟨221910053156633948427073777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295880070875511931236098369 221910053156633948427073777)
    ·
      refine ⟨166432539867475461320305333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221910053156633948427073777 166432539867475461320305333)
      ·
        refine ⟨15603050612575824498778625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166432539867475461320305333 15603050612575824498778625)
        ·
          refine ⟨11702287959431868374083969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15603050612575824498778625 11702287959431868374083969)
          ·
            refine ⟨8776715969573901280562977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702287959431868374083969 8776715969573901280562977)
            ·
              refine ⟨6582536977180425960422233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776715969573901280562977 6582536977180425960422233)
              ·
                refine ⟨4936902732885319470316675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582536977180425960422233 4936902732885319470316675)
                ·
                  refine ⟨7405354099327979205475013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936902732885319470316675 7405354099327979205475013)
                  ·
                    refine ⟨1388503893623996101026565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405354099327979205475013 1388503893623996101026565)
                    ·
                      rfl

theorem cell23_8112305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_8112305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112305 prefixEnd_8112305 := by exact prefixLift 8112305
  have htrace : WordTrace (prefixWord ++ tailWord_8112305) baseStart_8112305 baseEnd_8112305 := by
    simpa [prefixWord, tailWord_8112305, baseEnd_8112305] using wordTrace_append hprefix tailTrace_8112305
  have hstable : (prefixWord ++ tailWord_8112305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112305).length < 2 ^ (prefixWord ++ tailWord_8112305).sum := by decide
  have hdescent : baseEnd_8112305 < baseStart_8112305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112327 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 8, 4]
def baseStart_8112327 : Nat := 118140960795 + 8112327 * 2 ^ 59
def prefixEnd_8112327 : Nat := 4983230072969 + 3 ^ 40 * 8112327 * 2
def baseEnd_8112327 : Nat := 1388507659148795739001531

theorem tailTrace_8112327 : CollatzResearch.WordTrace tailWord_8112327 prefixEnd_8112327 1388507659148795739001531 := by
  unfold tailWord_8112327
  simp only [CollatzResearch.WordTrace]
  refine ⟨295880873281432228993399235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197253915520954819328932823 295880873281432228993399235)
  ·
    refine ⟨443821309922148343490098853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295880873281432228993399235 443821309922148343490098853)
    ·
      refine ⟨83216495610402814404393535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443821309922148343490098853 83216495610402814404393535)
      ·
        refine ⟨124824743415604221606590303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83216495610402814404393535 124824743415604221606590303)
        ·
          refine ⟨187237115123406332409885455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124824743415604221606590303 187237115123406332409885455)
          ·
            refine ⟨280855672685109498614828183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187237115123406332409885455 280855672685109498614828183)
            ·
              refine ⟨421283509027664247922242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280855672685109498614828183 421283509027664247922242275)
              ·
                refine ⟨631925263541496371883363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421283509027664247922242275 631925263541496371883363413)
                ·
                  refine ⟨7405374182126910608008165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 631925263541496371883363413 7405374182126910608008165)
                  ·
                    refine ⟨1388507659148795739001531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405374182126910608008165 1388507659148795739001531)
                    ·
                      rfl

theorem cell23_8112327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_8112327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112327 prefixEnd_8112327 := by exact prefixLift 8112327
  have htrace : WordTrace (prefixWord ++ tailWord_8112327) baseStart_8112327 baseEnd_8112327 := by
    simpa [prefixWord, tailWord_8112327, baseEnd_8112327] using wordTrace_append hprefix tailTrace_8112327
  have hstable : (prefixWord ++ tailWord_8112327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112327).length < 2 ^ (prefixWord ++ tailWord_8112327).sum := by decide
  have hdescent : baseEnd_8112327 < baseStart_8112327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112334 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_8112334 : Nat := 118140960795 + 8112334 * 2 ^ 59
def prefixEnd_8112334 : Nat := 4983230072969 + 3 ^ 40 * 8112334 * 2
def baseEnd_8112334 : Nat := 4165526571810968689617061

theorem tailTrace_8112334 : CollatzResearch.WordTrace tailWord_8112334 prefixEnd_8112334 4165526571810968689617061 := by
  unfold tailWord_8112334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36985141074050858648613007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197254085728271246125936037 36985141074050858648613007)
  ·
    refine ⟨55477711611076287972919511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36985141074050858648613007 55477711611076287972919511)
    ·
      refine ⟨83216567416614431959379267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55477711611076287972919511 83216567416614431959379267)
      ·
        refine ⟨124824851124921647939068901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83216567416614431959379267 124824851124921647939068901)
        ·
          refine ⟨23404659585922808988575419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124824851124921647939068901 23404659585922808988575419)
          ·
            refine ⟨35106989378884213482863129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23404659585922808988575419 35106989378884213482863129)
            ·
              refine ⟨26330242034163160112147347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35106989378884213482863129 26330242034163160112147347)
              ·
                refine ⟨39495363051244740168221021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26330242034163160112147347 39495363051244740168221021)
                ·
                  refine ⟨14810761144216777563082883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39495363051244740168221021 14810761144216777563082883)
                  ·
                    refine ⟨22216141716325166344624325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14810761144216777563082883 22216141716325166344624325)
                    ·
                      refine ⟨4165526571810968689617061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22216141716325166344624325 4165526571810968689617061)
                      ·
                        rfl

theorem cell23_8112334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_8112334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112334 prefixEnd_8112334 := by exact prefixLift 8112334
  have htrace : WordTrace (prefixWord ++ tailWord_8112334) baseStart_8112334 baseEnd_8112334 := by
    simpa [prefixWord, tailWord_8112334, baseEnd_8112334] using wordTrace_append hprefix tailTrace_8112334
  have hstable : (prefixWord ++ tailWord_8112334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112334).length < 2 ^ (prefixWord ++ tailWord_8112334).sum := by decide
  have hdescent : baseEnd_8112334 < baseStart_8112334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112338 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_8112338 : Nat := 118140960795 + 8112338 * 2 ^ 59
def prefixEnd_8112338 : Nat := 4983230072969 + 3 ^ 40 * 8112338 * 2
def baseEnd_8112338 : Nat := 4165528625733586673967043

theorem tailTrace_8112338 : CollatzResearch.WordTrace tailWord_8112338 prefixEnd_8112338 4165528625733586673967043 := by
  unfold tailWord_8112338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73970318621098094468012417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197254182989594918581366445 73970318621098094468012417)
  ·
    refine ⟨55477738965823570851009313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73970318621098094468012417 55477738965823570851009313)
    ·
      refine ⟨41608304224367678138256985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55477738965823570851009313 41608304224367678138256985)
      ·
        refine ⟨31206228168275758603692739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41608304224367678138256985 31206228168275758603692739)
        ·
          refine ⟨46809342252413637905539109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31206228168275758603692739 46809342252413637905539109)
          ·
            refine ⟨8776751672327557107288583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46809342252413637905539109 8776751672327557107288583)
            ·
              refine ⟨13165127508491335660932875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776751672327557107288583 13165127508491335660932875)
              ·
                refine ⟨19747691262737003491399313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165127508491335660932875 19747691262737003491399313)
                ·
                  refine ⟨14810768447052752618549485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19747691262737003491399313 14810768447052752618549485)
                  ·
                    refine ⟨5554038167644782231956057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810768447052752618549485 5554038167644782231956057)
                    ·
                      refine ⟨4165528625733586673967043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554038167644782231956057 4165528625733586673967043)
                      ·
                        rfl

theorem cell23_8112338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_8112338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112338 prefixEnd_8112338 := by exact prefixLift 8112338
  have htrace : WordTrace (prefixWord ++ tailWord_8112338) baseStart_8112338 baseEnd_8112338 := by
    simpa [prefixWord, tailWord_8112338, baseEnd_8112338] using wordTrace_append hprefix tailTrace_8112338
  have hstable : (prefixWord ++ tailWord_8112338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112338).length < 2 ^ (prefixWord ++ tailWord_8112338).sum := by decide
  have hdescent : baseEnd_8112338 < baseStart_8112338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112348 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_8112348 : Nat := 118140960795 + 8112348 * 2 ^ 59
def prefixEnd_8112348 : Nat := 4983230072969 + 3 ^ 40 * 8112348 * 2
def baseEnd_8112348 : Nat := 1388511253513377211613999

theorem tailTrace_8112348 : CollatzResearch.WordTrace tailWord_8112348 prefixEnd_8112348 1388511253513377211613999 := by
  unfold tailWord_8112348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147940819607178074789956849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197254426142904099719942465 147940819607178074789956849)
  ·
    refine ⟨110955614705383556092467637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147940819607178074789956849 110955614705383556092467637)
    ·
      refine ⟨10402088878629708383668841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110955614705383556092467637 10402088878629708383668841)
      ·
        refine ⟨7801566658972281287751631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402088878629708383668841 7801566658972281287751631)
        ·
          refine ⟨11702349988458421931627447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801566658972281287751631 11702349988458421931627447)
          ·
            refine ⟨17553524982687632897441171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702349988458421931627447 17553524982687632897441171)
            ·
              refine ⟨26330287474031449346161757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17553524982687632897441171 26330287474031449346161757)
              ·
                refine ⟨9873857802761793504810659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26330287474031449346161757 9873857802761793504810659)
                ·
                  refine ⟨14810786704142690257215989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873857802761793504810659 14810786704142690257215989)
                  ·
                    refine ⟨1388511253513377211613999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14810786704142690257215989 1388511253513377211613999)
                    ·
                      rfl

theorem cell23_8112348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_8112348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112348 prefixEnd_8112348 := by exact prefixLift 8112348
  have htrace : WordTrace (prefixWord ++ tailWord_8112348) baseStart_8112348 baseEnd_8112348 := by
    simpa [prefixWord, tailWord_8112348, baseEnd_8112348] using wordTrace_append hprefix tailTrace_8112348
  have hstable : (prefixWord ++ tailWord_8112348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112348).length < 2 ^ (prefixWord ++ tailWord_8112348).sum := by decide
  have hdescent : baseEnd_8112348 < baseStart_8112348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112357 : List Nat := [1, 3, 1, 4, 2, 2, 10]
def baseStart_8112357 : Nat := 118140960795 + 8112357 * 2 ^ 59
def prefixEnd_8112357 : Nat := 4983230072969 + 3 ^ 40 * 8112357 * 2
def baseEnd_8112357 : Nat := 51426399776123729625055

theorem tailTrace_8112357 : CollatzResearch.WordTrace tailWord_8112357 prefixEnd_8112357 51426399776123729625055 := by
  unfold tailWord_8112357
  simp only [CollatzResearch.WordTrace]
  refine ⟨295881967471323544116991325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197254644980882362744660883 295881967471323544116991325)
  ·
    refine ⟨110955737801746329043871747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295881967471323544116991325 110955737801746329043871747)
    ·
      refine ⟨166433606702619493565807621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110955737801746329043871747 166433606702619493565807621)
      ·
        refine ⟨31206301256741155043588929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166433606702619493565807621 31206301256741155043588929)
        ·
          refine ⟨23404725942555866282691697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31206301256741155043588929 23404725942555866282691697)
          ·
            refine ⟨17553544456916899712018773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23404725942555866282691697 17553544456916899712018773)
            ·
              refine ⟨51426399776123729625055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17553544456916899712018773 51426399776123729625055)
              ·
                rfl

theorem cell23_8112357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 10].length) (baseStart_8112357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112357 prefixEnd_8112357 := by exact prefixLift 8112357
  have htrace : WordTrace (prefixWord ++ tailWord_8112357) baseStart_8112357 baseEnd_8112357 := by
    simpa [prefixWord, tailWord_8112357, baseEnd_8112357] using wordTrace_append hprefix tailTrace_8112357
  have hstable : (prefixWord ++ tailWord_8112357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112357).length < 2 ^ (prefixWord ++ tailWord_8112357).sum := by decide
  have hdescent : baseEnd_8112357 < baseStart_8112357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112384 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_8112384 : Nat := 118140960795 + 8112384 * 2 ^ 59
def prefixEnd_8112384 : Nat := 4983230072969 + 3 ^ 40 * 8112384 * 2
def baseEnd_8112384 : Nat := 4165552245843693493991831

theorem tailTrace_8112384 : CollatzResearch.WordTrace tailWord_8112384 prefixEnd_8112384 4165552245843693493991831 := by
  unfold tailWord_8112384
  simp only [CollatzResearch.WordTrace]
  refine ⟨147941476121112863864112103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197255301494817151818816137 147941476121112863864112103)
  ·
    refine ⟨221912214181669295796168155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147941476121112863864112103 221912214181669295796168155)
    ·
      refine ⟨332868321272503943694252233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221912214181669295796168155 332868321272503943694252233)
      ·
        refine ⟨249651240954377957770689175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332868321272503943694252233 249651240954377957770689175)
        ·
          refine ⟨374476861431566936656033763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249651240954377957770689175 374476861431566936656033763)
          ·
            refine ⟨561715292147350404984050645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374476861431566936656033763 561715292147350404984050645)
            ·
              refine ⟨13165202159703525116813687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 561715292147350404984050645 13165202159703525116813687)
              ·
                refine ⟨19747803239555287675220531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165202159703525116813687 19747803239555287675220531)
                ·
                  refine ⟨29621704859332931512830797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19747803239555287675220531 29621704859332931512830797)
                  ·
                    refine ⟨11108139322249849317311549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29621704859332931512830797 11108139322249849317311549)
                    ·
                      refine ⟨4165552245843693493991831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108139322249849317311549 4165552245843693493991831)
                      ·
                        rfl

theorem cell23_8112384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_8112384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112384 prefixEnd_8112384 := by exact prefixLift 8112384
  have htrace : WordTrace (prefixWord ++ tailWord_8112384) baseStart_8112384 baseEnd_8112384 := by
    simpa [prefixWord, tailWord_8112384, baseEnd_8112384] using wordTrace_append hprefix tailTrace_8112384
  have hstable : (prefixWord ++ tailWord_8112384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112384).length < 2 ^ (prefixWord ++ tailWord_8112384).sum := by decide
  have hdescent : baseEnd_8112384 < baseStart_8112384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112388 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_8112388 : Nat := 118140960795 + 8112388 * 2 ^ 59
def prefixEnd_8112388 : Nat := 4983230072969 + 3 ^ 40 * 8112388 * 2
def baseEnd_8112388 : Nat := 4165554299766311478341813

theorem tailTrace_8112388 : CollatzResearch.WordTrace tailWord_8112388 prefixEnd_8112388 4165554299766311478341813 := by
  unfold tailWord_8112388
  simp only [CollatzResearch.WordTrace]
  refine ⟨147941549067105618205684909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197255398756140824274246545 147941549067105618205684909)
  ·
    refine ⟨55478080900164606827131841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147941549067105618205684909 55478080900164606827131841)
    ·
      refine ⟨41608560675123455120348881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55478080900164606827131841 41608560675123455120348881)
      ·
        refine ⟨31206420506342591340261661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41608560675123455120348881 31206420506342591340261661)
        ·
          refine ⟨11702407689878471752598123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31206420506342591340261661 11702407689878471752598123)
          ·
            refine ⟨17553611534817707628897185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702407689878471752598123 17553611534817707628897185)
            ·
              refine ⟨13165208651113280721672889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17553611534817707628897185 13165208651113280721672889)
              ·
                refine ⟨9873906488334960541254667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13165208651113280721672889 9873906488334960541254667)
                ·
                  refine ⟨14810859732502440811882001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873906488334960541254667 14810859732502440811882001)
                  ·
                    refine ⟨11108144799376830608911501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14810859732502440811882001 11108144799376830608911501)
                    ·
                      refine ⟨4165554299766311478341813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108144799376830608911501 4165554299766311478341813)
                      ·
                        rfl

theorem cell23_8112388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_8112388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112388 prefixEnd_8112388 := by exact prefixLift 8112388
  have htrace : WordTrace (prefixWord ++ tailWord_8112388) baseStart_8112388 baseEnd_8112388 := by
    simpa [prefixWord, tailWord_8112388, baseEnd_8112388] using wordTrace_append hprefix tailTrace_8112388
  have hstable : (prefixWord ++ tailWord_8112388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112388).length < 2 ^ (prefixWord ++ tailWord_8112388).sum := by decide
  have hdescent : baseEnd_8112388 < baseStart_8112388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112411 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 1, 3, 2]
def baseStart_8112411 : Nat := 118140960795 + 8112411 * 2 ^ 59
def prefixEnd_8112411 : Nat := 4983230072969 + 3 ^ 40 * 8112411 * 2
def baseEnd_8112411 : Nat := 4165566109821364888354207

theorem tailTrace_8112411 : CollatzResearch.WordTrace tailWord_8112411 prefixEnd_8112411 4165566109821364888354207 := by
  unfold tailWord_8112411
  simp only [CollatzResearch.WordTrace]
  refine ⟨295883937013127911339457087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197255958008751940892971391 295883937013127911339457087)
  ·
    refine ⟨443825905519691867009185631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295883937013127911339457087 443825905519691867009185631)
    ·
      refine ⟨665738858279537800513778447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443825905519691867009185631 665738858279537800513778447)
      ·
        refine ⟨998608287419306700770667671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665738858279537800513778447 998608287419306700770667671)
        ·
          refine ⟨1497912431128960051156001507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998608287419306700770667671 1497912431128960051156001507)
          ·
            refine ⟨2246868646693440076734002261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497912431128960051156001507 2246868646693440076734002261)
            ·
              refine ⟨26330491953438750899226589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2246868646693440076734002261 26330491953438750899226589)
              ·
                refine ⟨9873934482539531587209971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26330491953438750899226589 9873934482539531587209971)
                ·
                  refine ⟨14810901723809297380814957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873934482539531587209971 14810901723809297380814957)
                  ·
                    refine ⟨5554088146428486517805609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810901723809297380814957 5554088146428486517805609)
                    ·
                      refine ⟨4165566109821364888354207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554088146428486517805609 4165566109821364888354207)
                      ·
                        rfl

theorem cell23_8112411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 3, 2].length) (baseStart_8112411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112411 prefixEnd_8112411 := by exact prefixLift 8112411
  have htrace : WordTrace (prefixWord ++ tailWord_8112411) baseStart_8112411 baseEnd_8112411 := by
    simpa [prefixWord, tailWord_8112411, baseEnd_8112411] using wordTrace_append hprefix tailTrace_8112411
  have hstable : (prefixWord ++ tailWord_8112411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112411).length < 2 ^ (prefixWord ++ tailWord_8112411).sum := by decide
  have hdescent : baseEnd_8112411 < baseStart_8112411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112417 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_8112417 : Nat := 118140960795 + 8112417 * 2 ^ 59
def prefixEnd_8112417 : Nat := 4983230072969 + 3 ^ 40 * 8112417 * 2
def baseEnd_8112417 : Nat := 1388523063568430621626393

theorem tailTrace_8112417 : CollatzResearch.WordTrace tailWord_8112417 prefixEnd_8112417 1388523063568430621626393 := by
  unfold tailWord_8112417
  simp only [CollatzResearch.WordTrace]
  refine ⟨295884155851106174364175505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197256103900737449576117003 295884155851106174364175505)
  ·
    refine ⟨221913116888329630773131629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295884155851106174364175505 221913116888329630773131629)
    ·
      refine ⟨83217418833123611539924361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221913116888329630773131629 83217418833123611539924361)
      ·
        refine ⟨62413064124842708654943271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83217418833123611539924361 62413064124842708654943271)
        ·
          refine ⟨93619596187264062982414907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62413064124842708654943271 93619596187264062982414907)
          ·
            refine ⟨140429394280896094473622361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93619596187264062982414907 140429394280896094473622361)
            ·
              refine ⟨105322045710672070855216771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140429394280896094473622361 105322045710672070855216771)
              ·
                refine ⟨157983068566008106282825157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105322045710672070855216771 157983068566008106282825157)
                ·
                  refine ⟨29621825356126519928029717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157983068566008106282825157 29621825356126519928029717)
                  ·
                    refine ⟨1388523063568430621626393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29621825356126519928029717 1388523063568430621626393)
                    ·
                      rfl

theorem cell23_8112417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_8112417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112417 prefixEnd_8112417 := by exact prefixLift 8112417
  have htrace : WordTrace (prefixWord ++ tailWord_8112417) baseStart_8112417 baseEnd_8112417 := by
    simpa [prefixWord, tailWord_8112417, baseEnd_8112417] using wordTrace_append hprefix tailTrace_8112417
  have hstable : (prefixWord ++ tailWord_8112417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112417).length < 2 ^ (prefixWord ++ tailWord_8112417).sum := by decide
  have hdescent : baseEnd_8112417 < baseStart_8112417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112447 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 9]
def baseStart_8112447 : Nat := 118140960795 + 8112447 * 2 ^ 59
def prefixEnd_8112447 : Nat := 4983230072969 + 3 ^ 40 * 8112447 * 2
def baseEnd_8112447 : Nat := 462842732791658527500449

theorem tailTrace_8112447 : CollatzResearch.WordTrace tailWord_8112447 prefixEnd_8112447 462842732791658527500449 := by
  unfold tailWord_8112447
  simp only [CollatzResearch.WordTrace]
  refine ⟨295885250040997489487767595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197256833360664992991845063 295885250040997489487767595)
  ·
    refine ⟨443827875061496234231651393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295885250040997489487767595 443827875061496234231651393)
    ·
      refine ⟨332870906296122175673738545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443827875061496234231651393 332870906296122175673738545)
      ·
        refine ⟨249653179722091631755303909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332870906296122175673738545 249653179722091631755303909)
        ·
          refine ⟨46809971197892180954119483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249653179722091631755303909 46809971197892180954119483)
          ·
            refine ⟨70214956796838271431179225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46809971197892180954119483 70214956796838271431179225)
            ·
              refine ⟨52661217597628703573384419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70214956796838271431179225 52661217597628703573384419)
              ·
                refine ⟨78991826396443055360076629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52661217597628703573384419 78991826396443055360076629)
                ·
                  refine ⟨462842732791658527500449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78991826396443055360076629 462842732791658527500449)
                  ·
                    rfl

theorem cell23_8112447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 9].length) (baseStart_8112447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112447 prefixEnd_8112447 := by exact prefixLift 8112447
  have htrace : WordTrace (prefixWord ++ tailWord_8112447) baseStart_8112447 baseEnd_8112447 := by
    simpa [prefixWord, tailWord_8112447, baseEnd_8112447] using wordTrace_append hprefix tailTrace_8112447
  have hstable : (prefixWord ++ tailWord_8112447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112447).length < 2 ^ (prefixWord ++ tailWord_8112447).sum := by decide
  have hdescent : baseEnd_8112447 < baseStart_8112447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112474 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_8112474 : Nat := 118140960795 + 8112474 * 2 ^ 59
def prefixEnd_8112474 : Nat := 4983230072969 + 3 ^ 40 * 8112474 * 2
def baseEnd_8112474 : Nat := 4165598459102598141866417

theorem tailTrace_8112474 : CollatzResearch.WordTrace tailWord_8112474 prefixEnd_8112474 4165598459102598141866417 := by
  unfold tailWord_8112474
  simp only [CollatzResearch.WordTrace]
  refine ⟨73971558702974918274750119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197257489874599782066000317 73971558702974918274750119)
  ·
    refine ⟨110957338054462377412125179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73971558702974918274750119 110957338054462377412125179)
    ·
      refine ⟨166436007081693566118187769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110957338054462377412125179 166436007081693566118187769)
      ·
        refine ⟨124827005311270174588640827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166436007081693566118187769 124827005311270174588640827)
        ·
          refine ⟨187240507966905261882961241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124827005311270174588640827 187240507966905261882961241)
          ·
            refine ⟨140430380975178946412220931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187240507966905261882961241 140430380975178946412220931)
            ·
              refine ⟨210645571462768419618331397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140430380975178946412220931 210645571462768419618331397)
              ·
                refine ⟨39496044649269078678437137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210645571462768419618331397 39496044649269078678437137)
                ·
                  refine ⟨29622033486951809008827853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39496044649269078678437137 29622033486951809008827853)
                  ·
                    refine ⟨11108262557606928378310445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29622033486951809008827853 11108262557606928378310445)
                    ·
                      refine ⟨4165598459102598141866417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108262557606928378310445 4165598459102598141866417)
                      ·
                        rfl

theorem cell23_8112474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_8112474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112474 prefixEnd_8112474 := by exact prefixLift 8112474
  have htrace : WordTrace (prefixWord ++ tailWord_8112474) baseStart_8112474 baseEnd_8112474 := by
    simpa [prefixWord, tailWord_8112474, baseEnd_8112474] using wordTrace_append hprefix tailTrace_8112474
  have hstable : (prefixWord ++ tailWord_8112474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112474).length < 2 ^ (prefixWord ++ tailWord_8112474).sum := by decide
  have hdescent : baseEnd_8112474 < baseStart_8112474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112551 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_8112551 : Nat := 118140960795 + 8112551 * 2 ^ 59
def prefixEnd_8112551 : Nat := 4983230072969 + 3 ^ 40 * 8112551 * 2
def baseEnd_8112551 : Nat := 4165637997112994340603563

theorem tailTrace_8112551 : CollatzResearch.WordTrace tailWord_8112551 prefixEnd_8112551 4165637997112994340603563 := by
  unfold tailWord_8112551
  simp only [CollatzResearch.WordTrace]
  refine ⟨295889043232620715249553507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197259362155080476833035671 295889043232620715249553507)
  ·
    refine ⟨443833564848931072874330261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295889043232620715249553507 443833564848931072874330261)
    ·
      refine ⟨20804698352293644040984231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 443833564848931072874330261 20804698352293644040984231)
      ·
        refine ⟨31207047528440466061476347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20804698352293644040984231 31207047528440466061476347)
        ·
          refine ⟨46810571292660699092214521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31207047528440466061476347 46810571292660699092214521)
          ·
            refine ⟨35107928469495524319160891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46810571292660699092214521 35107928469495524319160891)
            ·
              refine ⟨52661892704243286478741337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35107928469495524319160891 52661892704243286478741337)
              ·
                refine ⟨39496419528182464859056003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52661892704243286478741337 39496419528182464859056003)
                ·
                  refine ⟨59244629292273697288584005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39496419528182464859056003 59244629292273697288584005)
                  ·
                    refine ⟨11108367992301318241609501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59244629292273697288584005 11108367992301318241609501)
                    ·
                      refine ⟨4165637997112994340603563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108367992301318241609501 4165637997112994340603563)
                      ·
                        rfl

theorem cell23_8112551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_8112551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112551 prefixEnd_8112551 := by exact prefixLift 8112551
  have htrace : WordTrace (prefixWord ++ tailWord_8112551) baseStart_8112551 baseEnd_8112551 := by
    simpa [prefixWord, tailWord_8112551, baseEnd_8112551] using wordTrace_append hprefix tailTrace_8112551
  have hstable : (prefixWord ++ tailWord_8112551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112551).length < 2 ^ (prefixWord ++ tailWord_8112551).sum := by decide
  have hdescent : baseEnd_8112551 < baseStart_8112551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112618 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_8112618 : Nat := 118140960795 + 8112618 * 2 ^ 59
def prefixEnd_8112618 : Nat := 4983230072969 + 3 ^ 40 * 8112618 * 2
def baseEnd_8112618 : Nat := 1388557466772281859488585

theorem tailTrace_8112618 : CollatzResearch.WordTrace tailWord_8112618 prefixEnd_8112618 1388557466772281859488585 := by
  unfold tailWord_8112618
  simp only [CollatzResearch.WordTrace]
  refine ⟨73972871730844496423060627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197260991282251990461495005 73972871730844496423060627)
  ·
    refine ⟨110959307596266744634590941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73972871730844496423060627 110959307596266744634590941)
    ·
      refine ⟨41609740348600029237971603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110959307596266744634590941 41609740348600029237971603)
      ·
        refine ⟨62414610522900043856957405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41609740348600029237971603 62414610522900043856957405)
        ·
          refine ⟨23405478946087516446359027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62414610522900043856957405 23405478946087516446359027)
          ·
            refine ⟨35108218419131274669538541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23405478946087516446359027 35108218419131274669538541)
            ·
              refine ⟨13165581907174228001076953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35108218419131274669538541 13165581907174228001076953)
              ·
                refine ⟨9874186430380671000807715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13165581907174228001076953 9874186430380671000807715)
                ·
                  refine ⟨14811279645571006501211573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874186430380671000807715 14811279645571006501211573)
                  ·
                    refine ⟨1388557466772281859488585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14811279645571006501211573 1388557466772281859488585)
                    ·
                      rfl

theorem cell23_8112618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_8112618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112618 prefixEnd_8112618 := by exact prefixLift 8112618
  have htrace : WordTrace (prefixWord ++ tailWord_8112618) baseStart_8112618 baseEnd_8112618 := by
    simpa [prefixWord, tailWord_8112618, baseEnd_8112618] using wordTrace_append hprefix tailTrace_8112618
  have hstable : (prefixWord ++ tailWord_8112618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112618).length < 2 ^ (prefixWord ++ tailWord_8112618).sum := by decide
  have hdescent : baseEnd_8112618 < baseStart_8112618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112634 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_8112634 : Nat := 118140960795 + 8112634 * 2 ^ 59
def prefixEnd_8112634 : Nat := 4983230072969 + 3 ^ 40 * 8112634 * 2
def baseEnd_8112634 : Nat := 4165680616007317515865681

theorem tailTrace_8112634 : CollatzResearch.WordTrace tailWord_8112634 prefixEnd_8112634 4165680616007317515865681 := by
  unfold tailWord_8112634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973017622830005106206239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197261380327546680283216637 73973017622830005106206239)
  ·
    refine ⟨110959526434245007659309359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73973017622830005106206239 110959526434245007659309359)
    ·
      refine ⟨166439289651367511488964039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110959526434245007659309359 166439289651367511488964039)
      ·
        refine ⟨249658934477051267233446059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166439289651367511488964039 249658934477051267233446059)
        ·
          refine ⟨374488401715576900850169089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249658934477051267233446059 374488401715576900850169089)
          ·
            refine ⟨280866301286682675637626817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374488401715576900850169089 280866301286682675637626817)
            ·
              refine ⟨210649725965012006728220113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280866301286682675637626817 210649725965012006728220113)
              ·
                refine ⟨157987294473759005046165085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210649725965012006728220113 157987294473759005046165085)
                ·
                  refine ⟨59245235427659626892311907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157987294473759005046165085 59245235427659626892311907)
                  ·
                    refine ⟨88867853141489440338467861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59245235427659626892311907 88867853141489440338467861)
                    ·
                      refine ⟨4165680616007317515865681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88867853141489440338467861 4165680616007317515865681)
                      ·
                        rfl

theorem cell23_8112634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_8112634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112634 prefixEnd_8112634 := by exact prefixLift 8112634
  have htrace : WordTrace (prefixWord ++ tailWord_8112634) baseStart_8112634 baseEnd_8112634 := by
    simpa [prefixWord, tailWord_8112634, baseEnd_8112634] using wordTrace_append hprefix tailTrace_8112634
  have hstable : (prefixWord ++ tailWord_8112634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112634).length < 2 ^ (prefixWord ++ tailWord_8112634).sum := by decide
  have hdescent : baseEnd_8112634 < baseStart_8112634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112668 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_8112668 : Nat := 118140960795 + 8112668 * 2 ^ 59
def prefixEnd_8112668 : Nat := 4983230072969 + 3 ^ 40 * 8112668 * 2
def baseEnd_8112668 : Nat := 4165698074349570382840525

theorem tailTrace_8112668 : CollatzResearch.WordTrace tailWord_8112668 prefixEnd_8112668 4165698074349570382840525 := by
  unfold tailWord_8112668
  simp only [CollatzResearch.WordTrace]
  refine ⟨147946655286598422115781329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197262207048797896154375105 147946655286598422115781329)
  ·
    refine ⟨110959991464948816586835997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147946655286598422115781329 110959991464948816586835997)
    ·
      refine ⟨41609996799355806220063499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110959991464948816586835997 41609996799355806220063499)
      ·
        refine ⟨62414995199033709330095249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41609996799355806220063499 62414995199033709330095249)
        ·
          refine ⟨46811246399275281997571437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62414995199033709330095249 46811246399275281997571437)
          ·
            refine ⟨17554217399728230749089289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46811246399275281997571437 17554217399728230749089289)
            ·
              refine ⟨13165663049796173061816967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17554217399728230749089289 13165663049796173061816967)
              ·
                refine ⟨19748494574694259592725451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165663049796173061816967 19748494574694259592725451)
                ·
                  refine ⟨29622741862041389389088177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19748494574694259592725451 29622741862041389389088177)
                  ·
                    refine ⟨22217056396531042041816133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29622741862041389389088177 22217056396531042041816133)
                    ·
                      refine ⟨4165698074349570382840525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22217056396531042041816133 4165698074349570382840525)
                      ·
                        rfl

theorem cell23_8112668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_8112668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112668 prefixEnd_8112668 := by exact prefixLift 8112668
  have htrace : WordTrace (prefixWord ++ tailWord_8112668) baseStart_8112668 baseEnd_8112668 := by
    simpa [prefixWord, tailWord_8112668, baseEnd_8112668] using wordTrace_append hprefix tailTrace_8112668
  have hstable : (prefixWord ++ tailWord_8112668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112668).length < 2 ^ (prefixWord ++ tailWord_8112668).sum := by decide
  have hdescent : baseEnd_8112668 < baseStart_8112668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112672 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8112672 : Nat := 118140960795 + 8112672 * 2 ^ 59
def prefixEnd_8112672 : Nat := 4983230072969 + 3 ^ 40 * 8112672 * 2
def baseEnd_8112672 : Nat := 4165700128272188367190507

theorem tailTrace_8112672 : CollatzResearch.WordTrace tailWord_8112672 prefixEnd_8112672 4165700128272188367190507 := by
  unfold tailWord_8112672
  simp only [CollatzResearch.WordTrace]
  refine ⟨147946728232591176457354135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197262304310121568609805513 147946728232591176457354135)
  ·
    refine ⟨221920092348886764686031203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147946728232591176457354135 221920092348886764686031203)
    ·
      refine ⟨332880138523330147029046805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221920092348886764686031203 332880138523330147029046805)
      ·
        refine ⟨15603756493281100641986569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332880138523330147029046805 15603756493281100641986569)
        ·
          refine ⟨11702817369960825481489927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15603756493281100641986569 11702817369960825481489927)
          ·
            refine ⟨17554226054941238222234891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702817369960825481489927 17554226054941238222234891)
            ·
              refine ⟨26331339082411857333352337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17554226054941238222234891 26331339082411857333352337)
              ·
                refine ⟨19748504311808893000014253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26331339082411857333352337 19748504311808893000014253)
                ·
                  refine ⟨7405689116928334875005345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19748504311808893000014253 7405689116928334875005345)
                  ·
                    refine ⟨5554266837696251156254009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7405689116928334875005345 5554266837696251156254009)
                    ·
                      refine ⟨4165700128272188367190507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554266837696251156254009 4165700128272188367190507)
                      ·
                        rfl

theorem cell23_8112672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8112672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112672 prefixEnd_8112672 := by exact prefixLift 8112672
  have htrace : WordTrace (prefixWord ++ tailWord_8112672) baseStart_8112672 baseEnd_8112672 := by
    simpa [prefixWord, tailWord_8112672, baseEnd_8112672] using wordTrace_append hprefix tailTrace_8112672
  have hstable : (prefixWord ++ tailWord_8112672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112672).length < 2 ^ (prefixWord ++ tailWord_8112672).sum := by decide
  have hdescent : baseEnd_8112672 < baseStart_8112672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112705 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_8112705 : Nat := 118140960795 + 8112705 * 2 ^ 59
def prefixEnd_8112705 : Nat := 4983230072969 + 3 ^ 40 * 8112705 * 2
def baseEnd_8112705 : Nat := 4165717073133786738077855

theorem tailTrace_8112705 : CollatzResearch.WordTrace tailWord_8112705 prefixEnd_8112705 4165717073133786738077855 := by
  unfold tailWord_8112705
  simp only [CollatzResearch.WordTrace]
  refine ⟨295894660074062799550659569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197263106716041866367106379 295894660074062799550659569)
  ·
    refine ⟨221920995055547099662994677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295894660074062799550659569 221920995055547099662994677)
    ·
      refine ⟨20805093286457540593405751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221920995055547099662994677 20805093286457540593405751)
      ·
        refine ⟨31207639929686310890108627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20805093286457540593405751 31207639929686310890108627)
        ·
          refine ⟨46811459894529466335162941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31207639929686310890108627 46811459894529466335162941)
          ·
            refine ⟨17554297460448549875686103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46811459894529466335162941 17554297460448549875686103)
            ·
              refine ⟨26331446190672824813529155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17554297460448549875686103 26331446190672824813529155)
              ·
                refine ⟨39497169286009237220293733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26331446190672824813529155 39497169286009237220293733)
                ·
                  refine ⟨7405719241126731978805075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39497169286009237220293733 7405719241126731978805075)
                  ·
                    refine ⟨11108578861690097968207613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7405719241126731978805075 11108578861690097968207613)
                    ·
                      refine ⟨4165717073133786738077855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108578861690097968207613 4165717073133786738077855)
                      ·
                        rfl

theorem cell23_8112705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_8112705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112705 prefixEnd_8112705 := by exact prefixLift 8112705
  have htrace : WordTrace (prefixWord ++ tailWord_8112705) baseStart_8112705 baseEnd_8112705 := by
    simpa [prefixWord, tailWord_8112705, baseEnd_8112705] using wordTrace_append hprefix tailTrace_8112705
  have hstable : (prefixWord ++ tailWord_8112705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112705).length < 2 ^ (prefixWord ++ tailWord_8112705).sum := by decide
  have hdescent : baseEnd_8112705 < baseStart_8112705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112721 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_8112721 : Nat := 118140960795 + 8112721 * 2 ^ 59
def prefixEnd_8112721 : Nat := 4983230072969 + 3 ^ 40 * 8112721 * 2
def baseEnd_8112721 : Nat := 1388575096274752891825927

theorem tailTrace_8112721 : CollatzResearch.WordTrace tailWord_8112721 prefixEnd_8112721 1388575096274752891825927 := by
  unfold tailWord_8112721
  simp only [CollatzResearch.WordTrace]
  refine ⟨295895243642004834283242017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197263495761336556188828011 295895243642004834283242017)
  ·
    refine ⟨221921432731503625712431513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295895243642004834283242017 221921432731503625712431513)
    ·
      refine ⟨166441074548627719284323635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221921432731503625712431513 166441074548627719284323635)
      ·
        refine ⟨249661611822941578926485453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166441074548627719284323635 249661611822941578926485453)
        ·
          refine ⟨93623104433603092097432045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249661611822941578926485453 93623104433603092097432045)
          ·
            refine ⟨35108664162601159536537017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93623104433603092097432045 35108664162601159536537017)
            ·
              refine ⟨26331498121950869652402763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35108664162601159536537017 26331498121950869652402763)
              ·
                refine ⟨39497247182926304478604145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26331498121950869652402763 39497247182926304478604145)
                ·
                  refine ⟨29622935387194728358953109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39497247182926304478604145 29622935387194728358953109)
                  ·
                    refine ⟨1388575096274752891825927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29622935387194728358953109 1388575096274752891825927)
                    ·
                      rfl

theorem cell23_8112721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_8112721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112721 prefixEnd_8112721 := by exact prefixLift 8112721
  have htrace : WordTrace (prefixWord ++ tailWord_8112721) baseStart_8112721 baseEnd_8112721 := by
    simpa [prefixWord, tailWord_8112721, baseEnd_8112721] using wordTrace_append hprefix tailTrace_8112721
  have hstable : (prefixWord ++ tailWord_8112721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112721).length < 2 ^ (prefixWord ++ tailWord_8112721).sum := by decide
  have hdescent : baseEnd_8112721 < baseStart_8112721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112722 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_8112722 : Nat := 118140960795 + 8112722 * 2 ^ 59
def prefixEnd_8112722 : Nat := 4983230072969 + 3 ^ 40 * 8112722 * 2
def baseEnd_8112722 : Nat := 4165725802304913171565277

theorem tailTrace_8112722 : CollatzResearch.WordTrace tailWord_8112722 prefixEnd_8112722 4165725802304913171565277 := by
  unfold tailWord_8112722
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973820028750302863507105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197263520076667474302685613 73973820028750302863507105)
  ·
    refine ⟨55480365021562727147630329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73973820028750302863507105 55480365021562727147630329)
    ·
      refine ⟨41610273766172045360722747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55480365021562727147630329 41610273766172045360722747)
      ·
        refine ⟨62415410649258068041084121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41610273766172045360722747 62415410649258068041084121)
        ·
          refine ⟨46811557986943551030813091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62415410649258068041084121 46811557986943551030813091)
          ·
            refine ⟨70217336980415326546219637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46811557986943551030813091 70217336980415326546219637)
            ·
              refine ⟨6582875341913936863708091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70217336980415326546219637 6582875341913936863708091)
              ·
                refine ⟨9874313012870905295562137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582875341913936863708091 9874313012870905295562137)
                ·
                  refine ⟨7405734759653178971671603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9874313012870905295562137 7405734759653178971671603)
                  ·
                    refine ⟨11108602139479768457507405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7405734759653178971671603 11108602139479768457507405)
                    ·
                      refine ⟨4165725802304913171565277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108602139479768457507405 4165725802304913171565277)
                      ·
                        rfl

theorem cell23_8112722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_8112722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112722 prefixEnd_8112722 := by exact prefixLift 8112722
  have htrace : WordTrace (prefixWord ++ tailWord_8112722) baseStart_8112722 baseEnd_8112722 := by
    simpa [prefixWord, tailWord_8112722, baseEnd_8112722] using wordTrace_append hprefix tailTrace_8112722
  have hstable : (prefixWord ++ tailWord_8112722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112722).length < 2 ^ (prefixWord ++ tailWord_8112722).sum := by decide
  have hdescent : baseEnd_8112722 < baseStart_8112722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112768 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 7]
def baseStart_8112768 : Nat := 118140960795 + 8112768 * 2 ^ 59
def prefixEnd_8112768 : Nat := 4983230072969 + 3 ^ 40 * 8112768 * 2
def baseEnd_8112768 : Nat := 462861046935002221287785

theorem tailTrace_8112768 : CollatzResearch.WordTrace tailWord_8112768 prefixEnd_8112768 462861046935002221287785 := by
  unfold tailWord_8112768
  simp only [CollatzResearch.WordTrace]
  refine ⟨147948478936417280655101479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197264638581889707540135305 147948478936417280655101479)
  ·
    refine ⟨221922718404625920982652219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147948478936417280655101479 221922718404625920982652219)
    ·
      refine ⟨332884077606938881473978329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221922718404625920982652219 332884077606938881473978329)
      ·
        refine ⟨249663058205204161105483747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332884077606938881473978329 249663058205204161105483747)
        ·
          refine ⟨374494587307806241658225621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249663058205204161105483747 374494587307806241658225621)
          ·
            refine ⟨8777216890026708788864663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374494587307806241658225621 8777216890026708788864663)
            ·
              refine ⟨13165825335040063183296995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8777216890026708788864663 13165825335040063183296995)
              ·
                refine ⟨19748738002560094774945493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165825335040063183296995 19748738002560094774945493)
                ·
                  refine ⟨462861046935002221287785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19748738002560094774945493 462861046935002221287785)
                  ·
                    rfl

theorem cell23_8112768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_8112768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112768 prefixEnd_8112768 := by exact prefixLift 8112768
  have htrace : WordTrace (prefixWord ++ tailWord_8112768) baseStart_8112768 baseEnd_8112768 := by
    simpa [prefixWord, tailWord_8112768, baseEnd_8112768] using wordTrace_append hprefix tailTrace_8112768
  have hstable : (prefixWord ++ tailWord_8112768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112768).length < 2 ^ (prefixWord ++ tailWord_8112768).sum := by decide
  have hdescent : baseEnd_8112768 < baseStart_8112768 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112791 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_8112791 : Nat := 118140960795 + 8112791 * 2 ^ 59
def prefixEnd_8112791 : Nat := 4983230072969 + 3 ^ 40 * 8112791 * 2
def baseEnd_8112791 : Nat := 4165761232470073401602459

theorem tailTrace_8112791 : CollatzResearch.WordTrace tailWord_8112791 prefixEnd_8112791 4165761232470073401602459 := by
  unfold tailWord_8112791
  simp only [CollatzResearch.WordTrace]
  refine ⟨295897796751751236238290227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197265197834500824158860151 295897796751751236238290227)
  ·
    refine ⟨443846695127626854357435341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295897796751751236238290227 443846695127626854357435341)
    ·
      refine ⟨166442510672860070384038253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443846695127626854357435341 166442510672860070384038253)
      ·
        refine ⟨62415941502322526394014345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166442510672860070384038253 62415941502322526394014345)
        ·
          refine ⟨46811956126741894795510759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62415941502322526394014345 46811956126741894795510759)
          ·
            refine ⟨70217934190112842193266139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46811956126741894795510759 70217934190112842193266139)
            ·
              refine ⟨105326901285169263289899209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70217934190112842193266139 105326901285169263289899209)
              ·
                refine ⟨78995175963876947467424407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105326901285169263289899209 78995175963876947467424407)
                ·
                  refine ⟨118492763945815421201136611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78995175963876947467424407 118492763945815421201136611)
                  ·
                    refine ⟨177739145918723131801704917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118492763945815421201136611 177739145918723131801704917)
                    ·
                      refine ⟨4165761232470073401602459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177739145918723131801704917 4165761232470073401602459)
                      ·
                        rfl

theorem cell23_8112791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_8112791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112791 prefixEnd_8112791 := by exact prefixLift 8112791
  have htrace : WordTrace (prefixWord ++ tailWord_8112791) baseStart_8112791 baseEnd_8112791 := by
    simpa [prefixWord, tailWord_8112791, baseEnd_8112791] using wordTrace_append hprefix tailTrace_8112791
  have hstable : (prefixWord ++ tailWord_8112791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112791).length < 2 ^ (prefixWord ++ tailWord_8112791).sum := by decide
  have hdescent : baseEnd_8112791 < baseStart_8112791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112855 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_8112855 : Nat := 118140960795 + 8112855 * 2 ^ 59
def prefixEnd_8112855 : Nat := 4983230072969 + 3 ^ 40 * 8112855 * 2
def baseEnd_8112855 : Nat := 4165794095231961151202165

theorem tailTrace_8112855 : CollatzResearch.WordTrace tailWord_8112855 prefixEnd_8112855 4165794095231961151202165 := by
  unfold tailWord_8112855
  simp only [CollatzResearch.WordTrace]
  refine ⟨295900131023519375168620019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197266754015679583445746679 295900131023519375168620019)
  ·
    refine ⟨443850196535279062752930029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295900131023519375168620019 443850196535279062752930029)
    ·
      refine ⟨166443823700729648532348761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443850196535279062752930029 166443823700729648532348761)
      ·
        refine ⟨124832867775547236399261571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166443823700729648532348761 124832867775547236399261571)
        ·
          refine ⟨187249301663320854598892357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124832867775547236399261571 187249301663320854598892357)
          ·
            refine ⟨35109244061872660237292317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187249301663320854598892357 35109244061872660237292317)
            ·
              refine ⟨13165966523202247588984619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35109244061872660237292317 13165966523202247588984619)
              ·
                refine ⟨19748949784803371383476929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165966523202247588984619 19748949784803371383476929)
                ·
                  refine ⟨14811712338602528537607697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19748949784803371383476929 14811712338602528537607697)
                  ·
                    refine ⟨11108784253951896403205773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14811712338602528537607697 11108784253951896403205773)
                    ·
                      refine ⟨4165794095231961151202165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108784253951896403205773 4165794095231961151202165)
                      ·
                        rfl

theorem cell23_8112855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_8112855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112855 prefixEnd_8112855 := by exact prefixLift 8112855
  have htrace : WordTrace (prefixWord ++ tailWord_8112855) baseStart_8112855 baseEnd_8112855 := by
    simpa [prefixWord, tailWord_8112855, baseEnd_8112855] using wordTrace_append hprefix tailTrace_8112855
  have hstable : (prefixWord ++ tailWord_8112855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112855).length < 2 ^ (prefixWord ++ tailWord_8112855).sum := by decide
  have hdescent : baseEnd_8112855 < baseStart_8112855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112878 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_8112878 : Nat := 118140960795 + 8112878 * 2 ^ 59
def prefixEnd_8112878 : Nat := 4983230072969 + 3 ^ 40 * 8112878 * 2
def baseEnd_8112878 : Nat := 4165805905287014561214559

theorem tailTrace_8112878 : CollatzResearch.WordTrace tailWord_8112878 prefixEnd_8112878 4165805905287014561214559 := by
  unfold tailWord_8112878
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987621237804506262088411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197267313268290700064471525 36987621237804506262088411)
  ·
    refine ⟨55481431856706759393132617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36987621237804506262088411 55481431856706759393132617)
    ·
      refine ⟨41611073892530069544849463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55481431856706759393132617 41611073892530069544849463)
      ·
        refine ⟨62416610838795104317274195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41611073892530069544849463 62416610838795104317274195)
        ·
          refine ⟨93624916258192656475911293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62416610838795104317274195 93624916258192656475911293)
          ·
            refine ⟨35109343596822246178466735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93624916258192656475911293 35109343596822246178466735)
            ·
              refine ⟨52664015395233369267700103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35109343596822246178466735 52664015395233369267700103)
              ·
                refine ⟨78996023092850053901550155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52664015395233369267700103 78996023092850053901550155)
                ·
                  refine ⟨118494034639275080852325233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78996023092850053901550155 118494034639275080852325233)
                  ·
                    refine ⟨88870525979456310639243925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118494034639275080852325233 88870525979456310639243925)
                    ·
                      refine ⟨4165805905287014561214559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88870525979456310639243925 4165805905287014561214559)
                      ·
                        rfl

theorem cell23_8112878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_8112878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112878 prefixEnd_8112878 := by exact prefixLift 8112878
  have htrace : WordTrace (prefixWord ++ tailWord_8112878) baseStart_8112878 baseEnd_8112878 := by
    simpa [prefixWord, tailWord_8112878, baseEnd_8112878] using wordTrace_append hprefix tailTrace_8112878
  have hstable : (prefixWord ++ tailWord_8112878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112878).length < 2 ^ (prefixWord ++ tailWord_8112878).sum := by decide
  have hdescent : baseEnd_8112878 < baseStart_8112878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112936 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_8112936 : Nat := 118140960795 + 8112936 * 2 ^ 59
def prefixEnd_8112936 : Nat := 4983230072969 + 3 ^ 40 * 8112936 * 2
def baseEnd_8112936 : Nat := 4165835687164975334289293

theorem tailTrace_8112936 : CollatzResearch.WordTrace tailWord_8112936 prefixEnd_8112936 4165835687164975334289293 := by
  unfold tailWord_8112936
  simp only [CollatzResearch.WordTrace]
  refine ⟨147951542668112963001159331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197268723557483950668212441 147951542668112963001159331)
  ·
    refine ⟨221927314002169444501738997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147951542668112963001159331 221927314002169444501738997)
    ·
      refine ⟨20805685687703385422038031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221927314002169444501738997 20805685687703385422038031)
      ·
        refine ⟨31208528531555078133057047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20805685687703385422038031 31208528531555078133057047)
        ·
          refine ⟨46812792797332617199585571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31208528531555078133057047 46812792797332617199585571)
          ·
            refine ⟨70219189195998925799378357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46812792797332617199585571 70219189195998925799378357)
            ·
              refine ⟨6583048987124899293691721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70219189195998925799378357 6583048987124899293691721)
              ·
                refine ⟨4937286740343674470268791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583048987124899293691721 4937286740343674470268791)
                ·
                  refine ⟨7405930110515511705403187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937286740343674470268791 7405930110515511705403187)
                  ·
                    refine ⟨11108895165773267558104781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7405930110515511705403187 11108895165773267558104781)
                    ·
                      refine ⟨4165835687164975334289293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108895165773267558104781 4165835687164975334289293)
                      ·
                        rfl

theorem cell23_8112936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_8112936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112936 prefixEnd_8112936 := by exact prefixLift 8112936
  have htrace : WordTrace (prefixWord ++ tailWord_8112936) baseStart_8112936 baseEnd_8112936 := by
    simpa [prefixWord, tailWord_8112936, baseEnd_8112936] using wordTrace_append hprefix tailTrace_8112936
  have hstable : (prefixWord ++ tailWord_8112936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112936).length < 2 ^ (prefixWord ++ tailWord_8112936).sum := by decide
  have hdescent : baseEnd_8112936 < baseStart_8112936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8112945 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_8112945 : Nat := 118140960795 + 8112945 * 2 ^ 59
def prefixEnd_8112945 : Nat := 4983230072969 + 3 ^ 40 * 8112945 * 2
def baseEnd_8112945 : Nat := 4165840308490865799076751

theorem tailTrace_8112945 : CollatzResearch.WordTrace tailWord_8112945 prefixEnd_8112945 4165840308490865799076751 := by
  unfold tailWord_8112945
  simp only [CollatzResearch.WordTrace]
  refine ⟨295903413593193320539396289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197268942395462213692930859 295903413593193320539396289)
  ·
    refine ⟨221927560194894990404547217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295903413593193320539396289 221927560194894990404547217)
    ·
      refine ⟨166445670146171242803410413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221927560194894990404547217 166445670146171242803410413)
      ·
        refine ⟨62417126304814216051278905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166445670146171242803410413 62417126304814216051278905)
        ·
          refine ⟨46812844728610662038459179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62417126304814216051278905 46812844728610662038459179)
          ·
            refine ⟨70219267092915993057688769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46812844728610662038459179 70219267092915993057688769)
            ·
              refine ⟨52664450319686994793266577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70219267092915993057688769 52664450319686994793266577)
              ·
                refine ⟨39498337739765246094949933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52664450319686994793266577 39498337739765246094949933)
                ·
                  refine ⟨14811876652411967285606225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39498337739765246094949933 14811876652411967285606225)
                  ·
                    refine ⟨11108907489308975464204669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14811876652411967285606225 11108907489308975464204669)
                    ·
                      refine ⟨4165840308490865799076751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11108907489308975464204669 4165840308490865799076751)
                      ·
                        rfl

theorem cell23_8112945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_8112945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8112945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8112945 prefixEnd_8112945 := by exact prefixLift 8112945
  have htrace : WordTrace (prefixWord ++ tailWord_8112945) baseStart_8112945 baseEnd_8112945 := by
    simpa [prefixWord, tailWord_8112945, baseEnd_8112945] using wordTrace_append hprefix tailTrace_8112945
  have hstable : (prefixWord ++ tailWord_8112945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8112945).length < 2 ^ (prefixWord ++ tailWord_8112945).sum := by decide
  have hdescent : baseEnd_8112945 < baseStart_8112945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8112945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113008 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_8113008 : Nat := 118140960795 + 8113008 * 2 ^ 59
def prefixEnd_8113008 : Nat := 4983230072969 + 3 ^ 40 * 8113008 * 2
def baseEnd_8113008 : Nat := 1388624219257366350862987

theorem tailTrace_8113008 : CollatzResearch.WordTrace tailWord_8113008 prefixEnd_8113008 1388624219257366350862987 := by
  unfold tailWord_8113008
  simp only [CollatzResearch.WordTrace]
  refine ⟨147952855695982541149469839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197270474261310054865959785 147952855695982541149469839)
  ·
    refine ⟨221929283543973811724204759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147952855695982541149469839 221929283543973811724204759)
    ·
      refine ⟨332893925315960717586307139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221929283543973811724204759 332893925315960717586307139)
      ·
        refine ⟨499340887973941076379460709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332893925315960717586307139 499340887973941076379460709)
        ·
          refine ⟨93626416495113951821148883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 499340887973941076379460709 93626416495113951821148883)
          ·
            refine ⟨140439624742670927731723325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93626416495113951821148883 140439624742670927731723325)
            ·
              refine ⟨52664859278501597899396247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140439624742670927731723325 52664859278501597899396247)
              ·
                refine ⟨78997288917752396849094371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52664859278501597899396247 78997288917752396849094371)
                ·
                  refine ⟨118495933376628595273641557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78997288917752396849094371 118495933376628595273641557)
                  ·
                    refine ⟨1388624219257366350862987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118495933376628595273641557 1388624219257366350862987)
                    ·
                      rfl

theorem cell23_8113008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_8113008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113008 prefixEnd_8113008 := by exact prefixLift 8113008
  have htrace : WordTrace (prefixWord ++ tailWord_8113008) baseStart_8113008 baseEnd_8113008 := by
    simpa [prefixWord, tailWord_8113008, baseEnd_8113008] using wordTrace_append hprefix tailTrace_8113008
  have hstable : (prefixWord ++ tailWord_8113008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113008).length < 2 ^ (prefixWord ++ tailWord_8113008).sum := by decide
  have hdescent : baseEnd_8113008 < baseStart_8113008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113045 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_8113045 : Nat := 118140960795 + 8113045 * 2 ^ 59
def prefixEnd_8113045 : Nat := 4983230072969 + 3 ^ 40 * 8113045 * 2
def baseEnd_8113045 : Nat := 4165891656556315407826291

theorem tailTrace_8113045 : CollatzResearch.WordTrace tailWord_8113045 prefixEnd_8113045 4165891656556315407826291 := by
  unfold tailWord_8113045
  simp only [CollatzResearch.WordTrace]
  refine ⟨295907060892831037618036589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197271373928554025078691059 295907060892831037618036589)
  ·
    refine ⟨110965147834811639106763721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295907060892831037618036589 110965147834811639106763721)
    ·
      refine ⟨83223860876108729330072791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110965147834811639106763721 83223860876108729330072791)
      ·
        refine ⟨124835791314163093995109187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83223860876108729330072791 124835791314163093995109187)
        ·
          refine ⟨187253686971244640992663781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124835791314163093995109187 187253686971244640992663781)
          ·
            refine ⟨35110066307108370186124459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187253686971244640992663781 35110066307108370186124459)
            ·
              refine ⟨52665099460662555279186689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35110066307108370186124459 52665099460662555279186689)
              ·
                refine ⟨39498824595496916459390017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52665099460662555279186689 39498824595496916459390017)
                ·
                  refine ⟨29624118446622687344542513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39498824595496916459390017 29624118446622687344542513)
                  ·
                    refine ⟨22218088834967015508406885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29624118446622687344542513 22218088834967015508406885)
                    ·
                      refine ⟨4165891656556315407826291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22218088834967015508406885 4165891656556315407826291)
                      ·
                        rfl

theorem cell23_8113045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_8113045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113045 prefixEnd_8113045 := by exact prefixLift 8113045
  have htrace : WordTrace (prefixWord ++ tailWord_8113045) baseStart_8113045 baseEnd_8113045 := by
    simpa [prefixWord, tailWord_8113045, baseEnd_8113045] using wordTrace_append hprefix tailTrace_8113045
  have hstable : (prefixWord ++ tailWord_8113045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113045).length < 2 ^ (prefixWord ++ tailWord_8113045).sum := by decide
  have hdescent : baseEnd_8113045 < baseStart_8113045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113055 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 7]
def baseStart_8113055 : Nat := 118140960795 + 8113055 * 2 ^ 59
def prefixEnd_8113055 : Nat := 4983230072969 + 3 ^ 40 * 8113055 * 2
def baseEnd_8113055 : Nat := 462877421262540040966805

theorem tailTrace_8113055 : CollatzResearch.WordTrace tailWord_8113055 prefixEnd_8113055 462877421262540040966805 := by
  unfold tailWord_8113055
  simp only [CollatzResearch.WordTrace]
  refine ⟨295907425622794809325900619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197271617081863206217267079 295907425622794809325900619)
  ·
    refine ⟨443861138434192213988850929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295907425622794809325900619 443861138434192213988850929)
    ·
      refine ⟨332895853825644160491638197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443861138434192213988850929 332895853825644160491638197)
      ·
        refine ⟨31208986296154140046091081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332895853825644160491638197 31208986296154140046091081)
        ·
          refine ⟨23406739722115605034568311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31208986296154140046091081 23406739722115605034568311)
          ·
            refine ⟨35110109583173407551852467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23406739722115605034568311 35110109583173407551852467)
            ·
              refine ⟨52665164374760111327778701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35110109583173407551852467 52665164374760111327778701)
              ·
                refine ⟨19749436640535041747917013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52665164374760111327778701 19749436640535041747917013)
                ·
                  refine ⟨462877421262540040966805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19749436640535041747917013 462877421262540040966805)
                  ·
                    rfl

theorem cell23_8113055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 7].length) (baseStart_8113055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113055 prefixEnd_8113055 := by exact prefixLift 8113055
  have htrace : WordTrace (prefixWord ++ tailWord_8113055) baseStart_8113055 baseEnd_8113055 := by
    simpa [prefixWord, tailWord_8113055, baseEnd_8113055] using wordTrace_append hprefix tailTrace_8113055
  have hstable : (prefixWord ++ tailWord_8113055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113055).length < 2 ^ (prefixWord ++ tailWord_8113055).sum := by decide
  have hdescent : baseEnd_8113055 < baseStart_8113055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113065 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_8113065 : Nat := 118140960795 + 8113065 * 2 ^ 59
def prefixEnd_8113065 : Nat := 4983230072969 + 3 ^ 40 * 8113065 * 2
def baseEnd_8113065 : Nat := 4165901926169405329576199

theorem tailTrace_8113065 : CollatzResearch.WordTrace tailWord_8113065 prefixEnd_8113065 4165901926169405329576199 := by
  unfold tailWord_8113065
  simp only [CollatzResearch.WordTrace]
  refine ⟨295907790352758581033764649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197271860235172387355843099 295907790352758581033764649)
  ·
    refine ⟨221930842764568935775323487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295907790352758581033764649 221930842764568935775323487)
    ·
      refine ⟨332896264146853403662985231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221930842764568935775323487 332896264146853403662985231)
      ·
        refine ⟨499344396220280105494477847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332896264146853403662985231 499344396220280105494477847)
        ·
          refine ⟨749016594330420158241716771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499344396220280105494477847 749016594330420158241716771)
          ·
            refine ⟨1123524891495630237362575157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749016594330420158241716771 1123524891495630237362575157)
            ·
              refine ⟨105330458577715334752741421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1123524891495630237362575157 105330458577715334752741421)
              ·
                refine ⟨39498921966643250532278033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105330458577715334752741421 39498921966643250532278033)
                ·
                  refine ⟨29624191474982437899208525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39498921966643250532278033 29624191474982437899208525)
                  ·
                    refine ⟨11109071803118414212203197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29624191474982437899208525 11109071803118414212203197)
                    ·
                      refine ⟨4165901926169405329576199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109071803118414212203197 4165901926169405329576199)
                      ·
                        rfl

theorem cell23_8113065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_8113065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113065 prefixEnd_8113065 := by exact prefixLift 8113065
  have htrace : WordTrace (prefixWord ++ tailWord_8113065) baseStart_8113065 baseEnd_8113065 := by
    simpa [prefixWord, tailWord_8113065, baseEnd_8113065] using wordTrace_append hprefix tailTrace_8113065
  have hstable : (prefixWord ++ tailWord_8113065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113065).length < 2 ^ (prefixWord ++ tailWord_8113065).sum := by decide
  have hdescent : baseEnd_8113065 < baseStart_8113065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113102 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_8113102 : Nat := 118140960795 + 8113102 * 2 ^ 59
def prefixEnd_8113102 : Nat := 4983230072969 + 3 ^ 40 * 8113102 * 2
def baseEnd_8113102 : Nat := 1388640308317873894937843

theorem tailTrace_8113102 : CollatzResearch.WordTrace tailWord_8113102 prefixEnd_8113102 1388640308317873894937843 := by
  unfold tailWord_8113102
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988642481703067044107695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197272759902416357568574373 36988642481703067044107695)
  ·
    refine ⟨55482963722554600566161543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988642481703067044107695 55482963722554600566161543)
    ·
      refine ⟨83224445583831900849242315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55482963722554600566161543 83224445583831900849242315)
      ·
        refine ⟨124836668375747851273863473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83224445583831900849242315 124836668375747851273863473)
        ·
          refine ⟨93627501281810888455397605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124836668375747851273863473 93627501281810888455397605)
          ·
            refine ⟨17555156490339541585387051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93627501281810888455397605 17555156490339541585387051)
            ·
              refine ⟨26332734735509312378080577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17555156490339541585387051 26332734735509312378080577)
              ·
                refine ⟨19749551051631984283560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26332734735509312378080577 19749551051631984283560433)
                ·
                  refine ⟨14812163288723988212670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19749551051631984283560433 14812163288723988212670325)
                  ·
                    refine ⟨1388640308317873894937843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14812163288723988212670325 1388640308317873894937843)
                    ·
                      rfl

theorem cell23_8113102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_8113102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113102 prefixEnd_8113102 := by exact prefixLift 8113102
  have htrace : WordTrace (prefixWord ++ tailWord_8113102) baseStart_8113102 baseEnd_8113102 := by
    simpa [prefixWord, tailWord_8113102, baseEnd_8113102] using wordTrace_append hprefix tailTrace_8113102
  have hstable : (prefixWord ++ tailWord_8113102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113102).length < 2 ^ (prefixWord ++ tailWord_8113102).sum := by decide
  have hdescent : baseEnd_8113102 < baseStart_8113102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113106 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_8113106 : Nat := 118140960795 + 8113106 * 2 ^ 59
def prefixEnd_8113106 : Nat := 4983230072969 + 3 ^ 40 * 8113106 * 2
def baseEnd_8113106 : Nat := 462880330986248852129279

theorem tailTrace_8113106 : CollatzResearch.WordTrace tailWord_8113106 prefixEnd_8113106 462880330986248852129279 := by
  unfold tailWord_8113106
  simp only [CollatzResearch.WordTrace]
  refine ⟨73977321436402511259001793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197272857163740030024004781 73977321436402511259001793)
  ·
    refine ⟨55482991077301883444251345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73977321436402511259001793 55482991077301883444251345)
    ·
      refine ⟨41612243307976412583188509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55482991077301883444251345 41612243307976412583188509)
      ·
        refine ⟨15604591240491154718695691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41612243307976412583188509 15604591240491154718695691)
        ·
          refine ⟨23406886860736732078043537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15604591240491154718695691 23406886860736732078043537)
          ·
            refine ⟨17555165145552549058532653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23406886860736732078043537 17555165145552549058532653)
            ·
              refine ⟨6583186929582205896949745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17555165145552549058532653 6583186929582205896949745)
              ·
                refine ⟨4937390197186654422712309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583186929582205896949745 4937390197186654422712309)
                ·
                  refine ⟨462880330986248852129279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4937390197186654422712309 462880330986248852129279)
                  ·
                    rfl

theorem cell23_8113106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_8113106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113106 prefixEnd_8113106 := by exact prefixLift 8113106
  have htrace : WordTrace (prefixWord ++ tailWord_8113106) baseStart_8113106 baseEnd_8113106 := by
    simpa [prefixWord, tailWord_8113106, baseEnd_8113106] using wordTrace_append hprefix tailTrace_8113106
  have hstable : (prefixWord ++ tailWord_8113106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113106).length < 2 ^ (prefixWord ++ tailWord_8113106).sum := by decide
  have hdescent : baseEnd_8113106 < baseStart_8113106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113149 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_8113149 : Nat := 118140960795 + 8113149 * 2 ^ 59
def prefixEnd_8113149 : Nat := 4983230072969 + 3 ^ 40 * 8113149 * 2
def baseEnd_8113149 : Nat := 1388648352848127666975271

theorem tailTrace_8113149 : CollatzResearch.WordTrace tailWord_8113149 prefixEnd_8113149 1388648352848127666975271 := by
  unfold tailWord_8113149
  simp only [CollatzResearch.WordTrace]
  refine ⟨295910854084454263379822501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197273902722969508919881667 295910854084454263379822501)
  ·
    refine ⟨55483285140835174383716719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295910854084454263379822501 55483285140835174383716719)
    ·
      refine ⟨83224927711252761575575079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55483285140835174383716719 83224927711252761575575079)
      ·
        refine ⟨124837391566879142363362619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83224927711252761575575079 124837391566879142363362619)
        ·
          refine ⟨187256087350318713545043929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124837391566879142363362619 187256087350318713545043929)
          ·
            refine ⟨140442065512739035158782947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187256087350318713545043929 140442065512739035158782947)
            ·
              refine ⟨210663098269108552738174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140442065512739035158782947 210663098269108552738174421)
              ·
                refine ⟨4937416365682231704800963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210663098269108552738174421 4937416365682231704800963)
                ·
                  refine ⟨7406124548523347557201445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937416365682231704800963 7406124548523347557201445)
                  ·
                    refine ⟨1388648352848127666975271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406124548523347557201445 1388648352848127666975271)
                    ·
                      rfl

theorem cell23_8113149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_8113149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113149 prefixEnd_8113149 := by exact prefixLift 8113149
  have htrace : WordTrace (prefixWord ++ tailWord_8113149) baseStart_8113149 baseEnd_8113149 := by
    simpa [prefixWord, tailWord_8113149, baseEnd_8113149] using wordTrace_append hprefix tailTrace_8113149
  have hstable : (prefixWord ++ tailWord_8113149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113149).length < 2 ^ (prefixWord ++ tailWord_8113149).sum := by decide
  have hdescent : baseEnd_8113149 < baseStart_8113149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113162 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_8113162 : Nat := 118140960795 + 8113162 * 2 ^ 59
def prefixEnd_8113162 : Nat := 4983230072969 + 3 ^ 40 * 8113162 * 2
def baseEnd_8113162 : Nat := 462883525976987938895917

theorem tailTrace_8113162 : CollatzResearch.WordTrace tailWord_8113162 prefixEnd_8113162 462883525976987938895917 := by
  unfold tailWord_8113162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73977832058351791650011435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197274218822271444400030493 73977832058351791650011435)
  ·
    refine ⟨110966748087527687475017153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73977832058351791650011435 110966748087527687475017153)
    ·
      refine ⟨83225061065645765606262865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110966748087527687475017153 83225061065645765606262865)
      ·
        refine ⟨62418795799234324204697149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83225061065645765606262865 62418795799234324204697149)
        ·
          refine ⟨23407048424712871576761431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62418795799234324204697149 23407048424712871576761431)
          ·
            refine ⟨35110572637069307365142147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23407048424712871576761431 35110572637069307365142147)
            ·
              refine ⟨52665858955603961047713221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35110572637069307365142147 52665858955603961047713221)
              ·
                refine ⟨9874848554175742696446229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52665858955603961047713221 9874848554175742696446229)
                ·
                  refine ⟨462883525976987938895917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9874848554175742696446229 462883525976987938895917)
                  ·
                    rfl

theorem cell23_8113162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_8113162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113162 prefixEnd_8113162 := by exact prefixLift 8113162
  have htrace : WordTrace (prefixWord ++ tailWord_8113162) baseStart_8113162 baseEnd_8113162 := by
    simpa [prefixWord, tailWord_8113162, baseEnd_8113162] using wordTrace_append hprefix tailTrace_8113162
  have hstable : (prefixWord ++ tailWord_8113162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113162).length < 2 ^ (prefixWord ++ tailWord_8113162).sum := by decide
  have hdescent : baseEnd_8113162 < baseStart_8113162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113166 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_8113166 : Nat := 118140960795 + 8113166 * 2 ^ 59
def prefixEnd_8113166 : Nat := 4983230072969 + 3 ^ 40 * 8113166 * 2
def baseEnd_8113166 : Nat := 1388651262571836478137745

theorem tailTrace_8113166 : CollatzResearch.WordTrace tailWord_8113166 prefixEnd_8113166 1388651262571836478137745 := by
  unfold tailWord_8113166
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988934265674084410398919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197274316083595116855460901 36988934265674084410398919)
  ·
    refine ⟨55483401398511126615598379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988934265674084410398919 55483401398511126615598379)
    ·
      refine ⟨83225102097766689923397569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55483401398511126615598379 83225102097766689923397569)
      ·
        refine ⟨62418826573325017442548177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83225102097766689923397569 62418826573325017442548177)
        ·
          refine ⟨46814119929993763081911133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62418826573325017442548177 46814119929993763081911133)
          ·
            refine ⟨17555294973747661155716675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46814119929993763081911133 17555294973747661155716675)
            ·
              refine ⟨26332942460621491733575013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17555294973747661155716675 26332942460621491733575013)
              ·
                refine ⟨4937426711366529700045315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26332942460621491733575013 4937426711366529700045315)
                ·
                  refine ⟨7406140067049794550067973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937426711366529700045315 7406140067049794550067973)
                  ·
                    refine ⟨1388651262571836478137745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406140067049794550067973 1388651262571836478137745)
                    ·
                      rfl

theorem cell23_8113166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_8113166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113166 prefixEnd_8113166 := by exact prefixLift 8113166
  have htrace : WordTrace (prefixWord ++ tailWord_8113166) baseStart_8113166 baseEnd_8113166 := by
    simpa [prefixWord, tailWord_8113166, baseEnd_8113166] using wordTrace_append hprefix tailTrace_8113166
  have hstable : (prefixWord ++ tailWord_8113166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113166).length < 2 ^ (prefixWord ++ tailWord_8113166).sum := by decide
  have hdescent : baseEnd_8113166 < baseStart_8113166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113189 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_8113189 : Nat := 118140960795 + 8113189 * 2 ^ 59
def prefixEnd_8113189 : Nat := 4983230072969 + 3 ^ 40 * 8113189 * 2
def baseEnd_8113189 : Nat := 4165965597770562844425629

theorem tailTrace_8113189 : CollatzResearch.WordTrace tailWord_8113189 prefixEnd_8113189 4165965597770562844425629 := by
  unfold tailWord_8113189
  simp only [CollatzResearch.WordTrace]
  refine ⟨295912313004309350211278621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197274875336206233474185747 295912313004309350211278621)
  ·
    refine ⟨110967117376616006329229483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295912313004309350211278621 110967117376616006329229483)
    ·
      refine ⟨166450676064924009493844225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110967117376616006329229483 166450676064924009493844225)
      ·
        refine ⟨124838007048693007120383169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166450676064924009493844225 124838007048693007120383169)
        ·
          refine ⟨93628505286519755340287377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124838007048693007120383169 93628505286519755340287377)
          ·
            refine ⟨70221378964889816505215533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93628505286519755340287377 70221378964889816505215533)
            ·
              refine ⟨26333017111833681189455825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70221378964889816505215533 26333017111833681189455825)
              ·
                refine ⟨19749762833875260892091869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26333017111833681189455825 19749762833875260892091869)
                ·
                  refine ⟨7406161062703222834534451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19749762833875260892091869 7406161062703222834534451)
                  ·
                    refine ⟨11109241594054834251801677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7406161062703222834534451 11109241594054834251801677)
                    ·
                      refine ⟨4165965597770562844425629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109241594054834251801677 4165965597770562844425629)
                      ·
                        rfl

theorem cell23_8113189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_8113189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113189 prefixEnd_8113189 := by exact prefixLift 8113189
  have htrace : WordTrace (prefixWord ++ tailWord_8113189) baseStart_8113189 baseEnd_8113189 := by
    simpa [prefixWord, tailWord_8113189, baseEnd_8113189] using wordTrace_append hprefix tailTrace_8113189
  have hstable : (prefixWord ++ tailWord_8113189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113189).length < 2 ^ (prefixWord ++ tailWord_8113189).sum := by decide
  have hdescent : baseEnd_8113189 < baseStart_8113189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113209 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_8113209 : Nat := 118140960795 + 8113209 * 2 ^ 59
def prefixEnd_8113209 : Nat := 4983230072969 + 3 ^ 40 * 8113209 * 2
def baseEnd_8113209 : Nat := 1388658622461217588725179

theorem tailTrace_8113209 : CollatzResearch.WordTrace tailWord_8113209 prefixEnd_8113209 1388658622461217588725179 := by
  unfold tailWord_8113209
  simp only [CollatzResearch.WordTrace]
  refine ⟨295913042464236893627006681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197275361642824595751337787 295913042464236893627006681)
  ·
    refine ⟨221934781848177670220255011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295913042464236893627006681 221934781848177670220255011)
    ·
      refine ⟨332902172772266505330382517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221934781848177670220255011 332902172772266505330382517)
      ·
        refine ⟨31209578697399984874723361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332902172772266505330382517 31209578697399984874723361)
        ·
          refine ⟨23407184023049988656042521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31209578697399984874723361 23407184023049988656042521)
          ·
            refine ⟨17555388017287491492031891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23407184023049988656042521 17555388017287491492031891)
            ·
              refine ⟨26333082025931237238047837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17555388017287491492031891 26333082025931237238047837)
              ·
                refine ⟨9874905759724213964267939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26333082025931237238047837 9874905759724213964267939)
                ·
                  refine ⟨14812358639586320946401909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874905759724213964267939 14812358639586320946401909)
                  ·
                    refine ⟨1388658622461217588725179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14812358639586320946401909 1388658622461217588725179)
                    ·
                      rfl

theorem cell23_8113209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_8113209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113209 prefixEnd_8113209 := by exact prefixLift 8113209
  have htrace : WordTrace (prefixWord ++ tailWord_8113209) baseStart_8113209 baseEnd_8113209 := by
    simpa [prefixWord, tailWord_8113209, baseEnd_8113209] using wordTrace_append hprefix tailTrace_8113209
  have hstable : (prefixWord ++ tailWord_8113209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113209).length < 2 ^ (prefixWord ++ tailWord_8113209).sum := by decide
  have hdescent : baseEnd_8113209 < baseStart_8113209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113232 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_8113232 : Nat := 118140960795 + 8113232 * 2 ^ 59
def prefixEnd_8113232 : Nat := 4983230072969 + 3 ^ 40 * 8113232 * 2
def baseEnd_8113232 : Nat := 4165987677438706176187931

theorem tailTrace_8113232 : CollatzResearch.WordTrace tailWord_8113232 prefixEnd_8113232 4165987677438706176187931 := by
  unfold tailWord_8113232
  simp only [CollatzResearch.WordTrace]
  refine ⟨147956940671576784277546975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197275920895435712370062633 147956940671576784277546975)
  ·
    refine ⟨221935411007365176416320463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147956940671576784277546975 221935411007365176416320463)
    ·
      refine ⟨332903116511047764624480695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221935411007365176416320463 332903116511047764624480695)
      ·
        refine ⟨499354674766571646936721043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332903116511047764624480695 499354674766571646936721043)
        ·
          refine ⟨749032012149857470405081565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499354674766571646936721043 749032012149857470405081565)
          ·
            refine ⟨280887004556196551401905587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749032012149857470405081565 280887004556196551401905587)
            ·
              refine ⟨421330506834294827102858381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280887004556196551401905587 421330506834294827102858381)
              ·
                refine ⟨157998940062860560163571893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421330506834294827102858381 157998940062860560163571893)
                ·
                  refine ⟨14812400630893177515334865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157998940062860560163571893 14812400630893177515334865)
                  ·
                    refine ⟨11109300473169883136501149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14812400630893177515334865 11109300473169883136501149)
                    ·
                      refine ⟨4165987677438706176187931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109300473169883136501149 4165987677438706176187931)
                      ·
                        rfl

theorem cell23_8113232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_8113232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113232 prefixEnd_8113232 := by exact prefixLift 8113232
  have htrace : WordTrace (prefixWord ++ tailWord_8113232) baseStart_8113232 baseEnd_8113232 := by
    simpa [prefixWord, tailWord_8113232, baseEnd_8113232] using wordTrace_append hprefix tailTrace_8113232
  have hstable : (prefixWord ++ tailWord_8113232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113232).length < 2 ^ (prefixWord ++ tailWord_8113232).sum := by decide
  have hdescent : baseEnd_8113232 < baseStart_8113232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113242 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_8113242 : Nat := 118140960795 + 8113242 * 2 ^ 59
def prefixEnd_8113242 : Nat := 4983230072969 + 3 ^ 40 * 8113242 * 2
def baseEnd_8113242 : Nat := 4165992812245251137062885

theorem tailTrace_8113242 : CollatzResearch.WordTrace tailWord_8113242 prefixEnd_8113242 4165992812245251137062885 := by
  unfold tailWord_8113242
  simp only [CollatzResearch.WordTrace]
  refine ⟨73978561518279335065739495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197276164048744893508638653 73978561518279335065739495)
  ·
    refine ⟨110967842277419002598609243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73978561518279335065739495 110967842277419002598609243)
    ·
      refine ⟨166451763416128503897913865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110967842277419002598609243 166451763416128503897913865)
      ·
        refine ⟨124838822562096377923435399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166451763416128503897913865 124838822562096377923435399)
        ·
          refine ⟨187258233843144566885153099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124838822562096377923435399 187258233843144566885153099)
          ·
            refine ⟨280887350764716850327729649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187258233843144566885153099 280887350764716850327729649)
            ·
              refine ⟨210665513073537637745797237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280887350764716850327729649 210665513073537637745797237)
              ·
                refine ⟨19749891850644153538668491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210665513073537637745797237 19749891850644153538668491)
                ·
                  refine ⟨29624837775966230308002737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19749891850644153538668491 29624837775966230308002737)
                  ·
                    refine ⟨22218628331974672731002053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29624837775966230308002737 22218628331974672731002053)
                    ·
                      refine ⟨4165992812245251137062885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22218628331974672731002053 4165992812245251137062885)
                      ·
                        rfl

theorem cell23_8113242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_8113242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113242 prefixEnd_8113242 := by exact prefixLift 8113242
  have htrace : WordTrace (prefixWord ++ tailWord_8113242) baseStart_8113242 baseEnd_8113242 := by
    simpa [prefixWord, tailWord_8113242, baseEnd_8113242] using wordTrace_append hprefix tailTrace_8113242
  have hstable : (prefixWord ++ tailWord_8113242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113242).length < 2 ^ (prefixWord ++ tailWord_8113242).sum := by decide
  have hdescent : baseEnd_8113242 < baseStart_8113242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113249 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_8113249 : Nat := 118140960795 + 8113249 * 2 ^ 59
def prefixEnd_8113249 : Nat := 4983230072969 + 3 ^ 40 * 8113249 * 2
def baseEnd_8113249 : Nat := 4165996406609832609675353

theorem tailTrace_8113249 : CollatzResearch.WordTrace tailWord_8113249 prefixEnd_8113249 4165996406609832609675353 := by
  unfold tailWord_8113249
  simp only [CollatzResearch.WordTrace]
  refine ⟨295914501384091980458462801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197276334256061320305641867 295914501384091980458462801)
  ·
    refine ⟨221935876038068985343847101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295914501384091980458462801 221935876038068985343847101)
    ·
      refine ⟨83225953514275869503942663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221935876038068985343847101 83225953514275869503942663)
      ·
        refine ⟨124838930271413804255913995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83225953514275869503942663 124838930271413804255913995)
        ·
          refine ⟨187258395407120706383870993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124838930271413804255913995 187258395407120706383870993)
          ·
            refine ⟨140443796555340529787903245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187258395407120706383870993 140443796555340529787903245)
            ·
              refine ⟨52666423708252698670463717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140443796555340529787903245 52666423708252698670463717)
              ·
                refine ⟨9874954445297381000711947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52666423708252698670463717 9874954445297381000711947)
                ·
                  refine ⟨14812431667946071501067921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874954445297381000711947 14812431667946071501067921)
                  ·
                    refine ⟨11109323750959553625800941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14812431667946071501067921 11109323750959553625800941)
                    ·
                      refine ⟨4165996406609832609675353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109323750959553625800941 4165996406609832609675353)
                      ·
                        rfl

theorem cell23_8113249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_8113249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113249 prefixEnd_8113249 := by exact prefixLift 8113249
  have htrace : WordTrace (prefixWord ++ tailWord_8113249) baseStart_8113249 baseEnd_8113249 := by
    simpa [prefixWord, tailWord_8113249, baseEnd_8113249] using wordTrace_append hprefix tailTrace_8113249
  have hstable : (prefixWord ++ tailWord_8113249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113249).length < 2 ^ (prefixWord ++ tailWord_8113249).sum := by decide
  have hdescent : baseEnd_8113249 < baseStart_8113249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113376 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 5]
def baseStart_8113376 : Nat := 118140960795 + 8113376 * 2 ^ 59
def prefixEnd_8113376 : Nat := 4983230072969 + 3 ^ 40 * 8113376 * 2
def baseEnd_8113376 : Nat := 462895735405883734754141

theorem tailTrace_8113376 : CollatzResearch.WordTrace tailWord_8113376 prefixEnd_8113376 462895735405883734754141 := by
  unfold tailWord_8113376
  simp only [CollatzResearch.WordTrace]
  refine ⟨147959566727315940574167991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197279422303087920765557321 147959566727315940574167991)
  ·
    refine ⟨221939350090973910861251987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147959566727315940574167991 221939350090973910861251987)
    ·
      refine ⟨332909025136460866291877981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221939350090973910861251987 332909025136460866291877981)
      ·
        refine ⟨124840884426172824859454243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332909025136460866291877981 124840884426172824859454243)
        ·
          refine ⟨187261326639259237289181365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124840884426172824859454243 187261326639259237289181365)
          ·
            refine ⟨17555749372430553495860753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187261326639259237289181365 17555749372430553495860753)
            ·
              refine ⟨13166812029322915121895565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17555749372430553495860753 13166812029322915121895565)
              ·
                refine ⟨4937554510996093170710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13166812029322915121895565 4937554510996093170710837)
                ·
                  refine ⟨462895735405883734754141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4937554510996093170710837 462895735405883734754141)
                  ·
                    rfl

theorem cell23_8113376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 5].length) (baseStart_8113376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113376 prefixEnd_8113376 := by exact prefixLift 8113376
  have htrace : WordTrace (prefixWord ++ tailWord_8113376) baseStart_8113376 baseEnd_8113376 := by
    simpa [prefixWord, tailWord_8113376, baseEnd_8113376] using wordTrace_append hprefix tailTrace_8113376
  have hstable : (prefixWord ++ tailWord_8113376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113376).length < 2 ^ (prefixWord ++ tailWord_8113376).sum := by decide
  have hdescent : baseEnd_8113376 < baseStart_8113376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113409 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_8113409 : Nat := 118140960795 + 8113409 * 2 ^ 59
def prefixEnd_8113409 : Nat := 4983230072969 + 3 ^ 40 * 8113409 * 2
def baseEnd_8113409 : Nat := 4166078563514551983674617

theorem tailTrace_8113409 : CollatzResearch.WordTrace tailWord_8113409 prefixEnd_8113409 4166078563514551983674617 := by
  unfold tailWord_8113409
  simp only [CollatzResearch.WordTrace]
  refine ⟨295920337063512327784287281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197280224709008218522858187 295920337063512327784287281)
  ·
    refine ⟨221940252797634245838215461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295920337063512327784287281 221940252797634245838215461)
    ·
      refine ⟨41613797399556421094665399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221940252797634245838215461 41613797399556421094665399)
      ·
        refine ⟨62420696099334631641998099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41613797399556421094665399 62420696099334631641998099)
        ·
          refine ⟨93631044149001947462997149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62420696099334631641998099 93631044149001947462997149)
          ·
            refine ⟨35111641555875730298623931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93631044149001947462997149 35111641555875730298623931)
            ·
              refine ⟨52667462333813595447935897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35111641555875730298623931 52667462333813595447935897)
              ·
                refine ⟨39500596750360196585951923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52667462333813595447935897 39500596750360196585951923)
                ·
                  refine ⟨59250895125540294878927885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39500596750360196585951923 59250895125540294878927885)
                  ·
                    refine ⟨22219085672077610579597957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59250895125540294878927885 22219085672077610579597957)
                    ·
                      refine ⟨4166078563514551983674617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22219085672077610579597957 4166078563514551983674617)
                      ·
                        rfl

theorem cell23_8113409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_8113409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113409 prefixEnd_8113409 := by exact prefixLift 8113409
  have htrace : WordTrace (prefixWord ++ tailWord_8113409) baseStart_8113409 baseEnd_8113409 := by
    simpa [prefixWord, tailWord_8113409, baseEnd_8113409] using wordTrace_append hprefix tailTrace_8113409
  have hstable : (prefixWord ++ tailWord_8113409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113409).length < 2 ^ (prefixWord ++ tailWord_8113409).sum := by decide
  have hdescent : baseEnd_8113409 < baseStart_8113409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113509 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_8113509 : Nat := 118140960795 + 8113509 * 2 ^ 59
def prefixEnd_8113509 : Nat := 4983230072969 + 3 ^ 40 * 8113509 * 2
def baseEnd_8113509 : Nat := 1388709970526667197474719

theorem tailTrace_8113509 : CollatzResearch.WordTrace tailWord_8113509 prefixEnd_8113509 1388709970526667197474719 := by
  unfold tailWord_8113509
  simp only [CollatzResearch.WordTrace]
  refine ⟨295923984363150044862927581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197282656242100029908618387 295923984363150044862927581)
  ·
    refine ⟨110971494136181266823597843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295923984363150044862927581 110971494136181266823597843)
    ·
      refine ⟨166457241204271900235396765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110971494136181266823597843 166457241204271900235396765)
      ·
        refine ⟨62421465451601962588273787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166457241204271900235396765 62421465451601962588273787)
        ·
          refine ⟨93632198177402943882410681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62421465451601962588273787 93632198177402943882410681)
          ·
            refine ⟨70224148633052207911808011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93632198177402943882410681 70224148633052207911808011)
            ·
              refine ⟨105336222949578311867712017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70224148633052207911808011 105336222949578311867712017)
              ·
                refine ⟨79002167212183733900784013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105336222949578311867712017 79002167212183733900784013)
                ·
                  refine ⟨29625812704568900212794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79002167212183733900784013 29625812704568900212794005)
                  ·
                    refine ⟨1388709970526667197474719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29625812704568900212794005 1388709970526667197474719)
                    ·
                      rfl

theorem cell23_8113509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_8113509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113509 prefixEnd_8113509 := by exact prefixLift 8113509
  have htrace : WordTrace (prefixWord ++ tailWord_8113509) baseStart_8113509 baseEnd_8113509 := by
    simpa [prefixWord, tailWord_8113509, baseEnd_8113509] using wordTrace_append hprefix tailTrace_8113509
  have hstable : (prefixWord ++ tailWord_8113509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113509).length < 2 ^ (prefixWord ++ tailWord_8113509).sum := by decide
  have hdescent : baseEnd_8113509 < baseStart_8113509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113516 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_8113516 : Nat := 118140960795 + 8113516 * 2 ^ 59
def prefixEnd_8113516 : Nat := 4983230072969 + 3 ^ 40 * 8113516 * 2
def baseEnd_8113516 : Nat := 4166133505944583065036625

theorem tailTrace_8113516 : CollatzResearch.WordTrace tailWord_8113516 prefixEnd_8113516 4166133505944583065036625 := by
  unfold tailWord_8113516
  simp only [CollatzResearch.WordTrace]
  refine ⟨147962119837062342529216201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197282826449416456705621601 147962119837062342529216201)
  ·
    refine ⟨110971589877796756896912151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147962119837062342529216201 110971589877796756896912151)
    ·
      refine ⟨166457384816695135345368227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110971589877796756896912151 166457384816695135345368227)
      ·
        refine ⟨249686077225042703018052341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166457384816695135345368227 249686077225042703018052341)
        ·
          refine ⟨23408069739847753407942407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249686077225042703018052341 23408069739847753407942407)
          ·
            refine ⟨35112104609771630111913611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23408069739847753407942407 35112104609771630111913611)
            ·
              refine ⟨52668156914657445167870417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35112104609771630111913611 52668156914657445167870417)
              ·
                refine ⟨39501117685993083875902813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52668156914657445167870417 39501117685993083875902813)
                ·
                  refine ⟨14812919132247406453463555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39501117685993083875902813 14812919132247406453463555)
                  ·
                    refine ⟨22219378698371109680195333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14812919132247406453463555 22219378698371109680195333)
                    ·
                      refine ⟨4166133505944583065036625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22219378698371109680195333 4166133505944583065036625)
                      ·
                        rfl

theorem cell23_8113516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_8113516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113516 prefixEnd_8113516 := by exact prefixLift 8113516
  have htrace : WordTrace (prefixWord ++ tailWord_8113516) baseStart_8113516 baseEnd_8113516 := by
    simpa [prefixWord, tailWord_8113516, baseEnd_8113516] using wordTrace_append hprefix tailTrace_8113516
  have hstable : (prefixWord ++ tailWord_8113516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113516).length < 2 ^ (prefixWord ++ tailWord_8113516).sum := by decide
  have hdescent : baseEnd_8113516 < baseStart_8113516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113519 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_8113519 : Nat := 118140960795 + 8113519 * 2 ^ 59
def prefixEnd_8113519 : Nat := 4983230072969 + 3 ^ 40 * 8113519 * 2
def baseEnd_8113519 : Nat := 4166135046386546553299111

theorem tailTrace_8113519 : CollatzResearch.WordTrace tailWord_8113519 prefixEnd_8113519 4166135046386546553299111 := by
  unfold tailWord_8113519
  simp only [CollatzResearch.WordTrace]
  refine ⟨295924349093113816570791611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197282899395409211047194407 295924349093113816570791611)
  ·
    refine ⟨443886523639670724856187417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295924349093113816570791611 443886523639670724856187417)
    ·
      refine ⟨332914892729753043642140563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443886523639670724856187417 332914892729753043642140563)
      ·
        refine ⟨499372339094629565463210845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332914892729753043642140563 499372339094629565463210845)
        ·
          refine ⟨187264627160486087048704067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499372339094629565463210845 187264627160486087048704067)
          ·
            refine ⟨280896940740729130573056101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187264627160486087048704067 280896940740729130573056101)
            ·
              refine ⟨52668176388886711982448019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280896940740729130573056101 52668176388886711982448019)
              ·
                refine ⟨79002264583330067973672029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52668176388886711982448019 79002264583330067973672029)
                ·
                  refine ⟨29625849218748775490127011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79002264583330067973672029 29625849218748775490127011)
                  ·
                    refine ⟨44438773828123163235190517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29625849218748775490127011 44438773828123163235190517)
                    ·
                      refine ⟨4166135046386546553299111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44438773828123163235190517 4166135046386546553299111)
                      ·
                        rfl

theorem cell23_8113519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_8113519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113519 prefixEnd_8113519 := by exact prefixLift 8113519
  have htrace : WordTrace (prefixWord ++ tailWord_8113519) baseStart_8113519 baseEnd_8113519 := by
    simpa [prefixWord, tailWord_8113519, baseEnd_8113519] using wordTrace_append hprefix tailTrace_8113519
  have hstable : (prefixWord ++ tailWord_8113519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113519).length < 2 ^ (prefixWord ++ tailWord_8113519).sum := by decide
  have hdescent : baseEnd_8113519 < baseStart_8113519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113529 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_8113529 : Nat := 118140960795 + 8113529 * 2 ^ 59
def prefixEnd_8113529 : Nat := 4983230072969 + 3 ^ 40 * 8113529 * 2
def baseEnd_8113529 : Nat := 4166140181193091514174065

theorem tailTrace_8113529 : CollatzResearch.WordTrace tailWord_8113529 prefixEnd_8113529 4166140181193091514174065 := by
  unfold tailWord_8113529
  simp only [CollatzResearch.WordTrace]
  refine ⟨295924713823077588278655641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197283142548718392185770427 295924713823077588278655641)
  ·
    refine ⟨221943535367308191208991731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295924713823077588278655641 221943535367308191208991731)
    ·
      refine ⟨332915303050962286813487597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221943535367308191208991731 332915303050962286813487597)
      ·
        refine ⟨124843238644110857555057849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332915303050962286813487597 124843238644110857555057849)
        ·
          refine ⟨93632428983083143166293387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124843238644110857555057849 93632428983083143166293387)
          ·
            refine ⟨140448643474624714749440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93632428983083143166293387 140448643474624714749440081)
            ·
              refine ⟨105336482605968536062080061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140448643474624714749440081 105336482605968536062080061)
              ·
                refine ⟨39501180977238201023280023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105336482605968536062080061 39501180977238201023280023)
                ·
                  refine ⟨59251771465857301534920035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39501180977238201023280023 59251771465857301534920035)
                  ·
                    refine ⟨88877657198785952302380053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59251771465857301534920035 88877657198785952302380053)
                    ·
                      refine ⟨4166140181193091514174065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88877657198785952302380053 4166140181193091514174065)
                      ·
                        rfl

theorem cell23_8113529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_8113529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113529 prefixEnd_8113529 := by exact prefixLift 8113529
  have htrace : WordTrace (prefixWord ++ tailWord_8113529) baseStart_8113529 baseEnd_8113529 := by
    simpa [prefixWord, tailWord_8113529, baseEnd_8113529] using wordTrace_append hprefix tailTrace_8113529
  have hstable : (prefixWord ++ tailWord_8113529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113529).length < 2 ^ (prefixWord ++ tailWord_8113529).sum := by decide
  have hdescent : baseEnd_8113529 < baseStart_8113529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113537 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_8113537 : Nat := 118140960795 + 8113537 * 2 ^ 59
def prefixEnd_8113537 : Nat := 4983230072969 + 3 ^ 40 * 8113537 * 2
def baseEnd_8113537 : Nat := 4166144289038327482874029

theorem tailTrace_8113537 : CollatzResearch.WordTrace tailWord_8113537 prefixEnd_8113537 4166144289038327482874029 := by
  unfold tailWord_8113537
  simp only [CollatzResearch.WordTrace]
  refine ⟨295925005607048605644946865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197283337071365737096631243 295925005607048605644946865)
  ·
    refine ⟨221943754205286454233710149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295925005607048605644946865 221943754205286454233710149)
    ·
      refine ⟨41614453913491210168820653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221943754205286454233710149 41614453913491210168820653)
      ·
        refine ⟨15605420217559203813307745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41614453913491210168820653 15605420217559203813307745)
        ·
          refine ⟨11704065163169402859980809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15605420217559203813307745 11704065163169402859980809)
          ·
            refine ⟨8778048872377052144985607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704065163169402859980809 8778048872377052144985607)
            ·
              refine ⟨13167073308565578217478411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778048872377052144985607 13167073308565578217478411)
              ·
                refine ⟨19750609962848367326217617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167073308565578217478411 19750609962848367326217617)
                ·
                  refine ⟨14812957472136275494663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19750609962848367326217617 14812957472136275494663213)
                  ·
                    refine ⟨5554859052051103310498705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14812957472136275494663213 5554859052051103310498705)
                    ·
                      refine ⟨4166144289038327482874029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554859052051103310498705 4166144289038327482874029)
                      ·
                        rfl

theorem cell23_8113537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_8113537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113537 prefixEnd_8113537 := by exact prefixLift 8113537
  have htrace : WordTrace (prefixWord ++ tailWord_8113537) baseStart_8113537 baseEnd_8113537 := by
    simpa [prefixWord, tailWord_8113537, baseEnd_8113537] using wordTrace_append hprefix tailTrace_8113537
  have hstable : (prefixWord ++ tailWord_8113537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113537).length < 2 ^ (prefixWord ++ tailWord_8113537).sum := by decide
  have hdescent : baseEnd_8113537 < baseStart_8113537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113550 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_8113550 : Nat := 118140960795 + 8113550 * 2 ^ 59
def prefixEnd_8113550 : Nat := 4983230072969 + 3 ^ 40 * 8113550 * 2
def baseEnd_8113550 : Nat := 4166150964286835932011469

theorem tailTrace_8113550 : CollatzResearch.WordTrace tailWord_8113550 prefixEnd_8113550 4166150964286835932011469 := by
  unfold tailWord_8113550
  simp only [CollatzResearch.WordTrace]
  refine ⟨36990684969500188608146263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197283653170667672576780069 36990684969500188608146263)
  ·
    refine ⟨55486027454250282912219395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36990684969500188608146263 55486027454250282912219395)
    ·
      refine ⟨83229041181375424368329093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55486027454250282912219395 83229041181375424368329093)
      ·
        refine ⟨15605445221507892069061705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83229041181375424368329093 15605445221507892069061705)
        ·
          refine ⟨11704083916130919051796279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15605445221507892069061705 11704083916130919051796279)
          ·
            refine ⟨17556125874196378577694419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704083916130919051796279 17556125874196378577694419)
            ·
              refine ⟨26334188811294567866541629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556125874196378577694419 26334188811294567866541629)
              ·
                refine ⟨9875320804235462949953111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26334188811294567866541629 9875320804235462949953111)
                ·
                  refine ⟨14812981206353194424929667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875320804235462949953111 14812981206353194424929667)
                  ·
                    refine ⟨22219471809529791637394501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14812981206353194424929667 22219471809529791637394501)
                    ·
                      refine ⟨4166150964286835932011469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22219471809529791637394501 4166150964286835932011469)
                      ·
                        rfl

theorem cell23_8113550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_8113550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113550 prefixEnd_8113550 := by exact prefixLift 8113550
  have htrace : WordTrace (prefixWord ++ tailWord_8113550) baseStart_8113550 baseEnd_8113550 := by
    simpa [prefixWord, tailWord_8113550, baseEnd_8113550] using wordTrace_append hprefix tailTrace_8113550
  have hstable : (prefixWord ++ tailWord_8113550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113550).length < 2 ^ (prefixWord ++ tailWord_8113550).sum := by decide
  have hdescent : baseEnd_8113550 < baseStart_8113550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113556 : List Nat := [2, 4, 2, 1, 2, 2, 10]
def baseStart_8113556 : Nat := 118140960795 + 8113556 * 2 ^ 59
def prefixEnd_8113556 : Nat := 4983230072969 + 3 ^ 40 * 8113556 * 2
def baseEnd_8113556 : Nat := 51434000557663739611561

theorem tailTrace_8113556 : CollatzResearch.WordTrace tailWord_8113556 prefixEnd_8113556 51434000557663739611561 := by
  unfold tailWord_8113556
  simp only [CollatzResearch.WordTrace]
  refine ⟨147962849296989885944944261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197283799062653181259925681 147962849296989885944944261)
  ·
    refine ⟨27743034243185603614677049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147962849296989885944944261 27743034243185603614677049)
    ·
      refine ⟨20807275682389202711007787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27743034243185603614677049 20807275682389202711007787)
      ·
        refine ⟨31210913523583804066511681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20807275682389202711007787 31210913523583804066511681)
        ·
          refine ⟨23408185142687853049883761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31210913523583804066511681 23408185142687853049883761)
          ·
            refine ⟨17556138857015889787412821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23408185142687853049883761 17556138857015889787412821)
            ·
              refine ⟨51434000557663739611561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17556138857015889787412821 51434000557663739611561)
              ·
                rfl

theorem cell23_8113556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 10].length) (baseStart_8113556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113556 prefixEnd_8113556 := by exact prefixLift 8113556
  have htrace : WordTrace (prefixWord ++ tailWord_8113556) baseStart_8113556 baseEnd_8113556 := by
    simpa [prefixWord, tailWord_8113556, baseEnd_8113556] using wordTrace_append hprefix tailTrace_8113556
  have hstable : (prefixWord ++ tailWord_8113556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113556).length < 2 ^ (prefixWord ++ tailWord_8113556).sum := by decide
  have hdescent : baseEnd_8113556 < baseStart_8113556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113559 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_8113559 : Nat := 118140960795 + 8113559 * 2 ^ 59
def prefixEnd_8113559 : Nat := 4983230072969 + 3 ^ 40 * 8113559 * 2
def baseEnd_8113559 : Nat := 4166155585612726396798927

theorem tailTrace_8113559 : CollatzResearch.WordTrace tailWord_8113559 prefixEnd_8113559 4166155585612726396798927 := by
  unfold tailWord_8113559
  simp only [CollatzResearch.WordTrace]
  refine ⟨295925808012968903402247731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197283872008645935601498487 295925808012968903402247731)
  ·
    refine ⟨443888712019453355103371597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295925808012968903402247731 443888712019453355103371597)
    ·
      refine ⟨166458267007295008163764349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443888712019453355103371597 166458267007295008163764349)
      ·
        refine ⟨62421850127735628061411631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166458267007295008163764349 62421850127735628061411631)
        ·
          refine ⟨93632775191603442092117447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62421850127735628061411631 93632775191603442092117447)
          ·
            refine ⟨140449162787405163138176171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93632775191603442092117447 140449162787405163138176171)
            ·
              refine ⟨210673744181107744707264257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140449162787405163138176171 210673744181107744707264257)
              ·
                refine ⟨158005308135830808530448193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210673744181107744707264257 158005308135830808530448193)
                ·
                  refine ⟨118503981101873106397836145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158005308135830808530448193 118503981101873106397836145)
                  ·
                    refine ⟨88877985826404829798377109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118503981101873106397836145 88877985826404829798377109)
                    ·
                      refine ⟨4166155585612726396798927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88877985826404829798377109 4166155585612726396798927)
                      ·
                        rfl

theorem cell23_8113559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_8113559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113559 prefixEnd_8113559 := by exact prefixLift 8113559
  have htrace : WordTrace (prefixWord ++ tailWord_8113559) baseStart_8113559 baseEnd_8113559 := by
    simpa [prefixWord, tailWord_8113559, baseEnd_8113559] using wordTrace_append hprefix tailTrace_8113559
  have hstable : (prefixWord ++ tailWord_8113559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113559).length < 2 ^ (prefixWord ++ tailWord_8113559).sum := by decide
  have hdescent : baseEnd_8113559 < baseStart_8113559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113567 : List Nat := [1, 1, 2, 5, 1, 2, 2, 4, 1, 2, 2]
def baseStart_8113567 : Nat := 118140960795 + 8113567 * 2 ^ 59
def prefixEnd_8113567 : Nat := 4983230072969 + 3 ^ 40 * 8113567 * 2
def baseEnd_8113567 : Nat := 4166159693457962365498891

theorem tailTrace_8113567 : CollatzResearch.WordTrace tailWord_8113567 prefixEnd_8113567 4166159693457962365498891 := by
  unfold tailWord_8113567
  simp only [CollatzResearch.WordTrace]
  refine ⟨295926099796939920768538955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197284066531293280512359303 295926099796939920768538955)
  ·
    refine ⟨443889149695409881152808433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295926099796939920768538955 443889149695409881152808433)
    ·
      refine ⟨332916862271557410864606325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443889149695409881152808433 332916862271557410864606325)
      ·
        refine ⟨31210955837958507268556843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332916862271557410864606325 31210955837958507268556843)
        ·
          refine ⟨46816433756937760902835265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31210955837958507268556843 46816433756937760902835265)
          ·
            refine ⟨35112325317703320677126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46816433756937760902835265 35112325317703320677126449)
            ·
              refine ⟨26334243988277490507844837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35112325317703320677126449 26334243988277490507844837)
              ·
                refine ⟨4937670747802029470220907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26334243988277490507844837 4937670747802029470220907)
                ·
                  refine ⟨7406506121703044205331361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937670747802029470220907 7406506121703044205331361)
                  ·
                    refine ⟨5554879591277283153998521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7406506121703044205331361 5554879591277283153998521)
                    ·
                      refine ⟨4166159693457962365498891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554879591277283153998521 4166159693457962365498891)
                      ·
                        rfl

theorem cell23_8113567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_8113567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113567 prefixEnd_8113567 := by exact prefixLift 8113567
  have htrace : WordTrace (prefixWord ++ tailWord_8113567) baseStart_8113567 baseEnd_8113567 := by
    simpa [prefixWord, tailWord_8113567, baseEnd_8113567] using wordTrace_append hprefix tailTrace_8113567
  have hstable : (prefixWord ++ tailWord_8113567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113567).length < 2 ^ (prefixWord ++ tailWord_8113567).sum := by decide
  have hdescent : baseEnd_8113567 < baseStart_8113567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113583 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_8113583 : Nat := 118140960795 + 8113583 * 2 ^ 59
def prefixEnd_8113583 : Nat := 4983230072969 + 3 ^ 40 * 8113583 * 2
def baseEnd_8113583 : Nat := 4166167909148434302898817

theorem tailTrace_8113583 : CollatzResearch.WordTrace tailWord_8113583 prefixEnd_8113583 4166167909148434302898817 := by
  unfold tailWord_8113583
  simp only [CollatzResearch.WordTrace]
  refine ⟨295926683364881955501121403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197284455576587970334080935 295926683364881955501121403)
  ·
    refine ⟨443890025047322933251682105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295926683364881955501121403 443890025047322933251682105)
    ·
      refine ⟨332917518785492199938761579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443890025047322933251682105 332917518785492199938761579)
      ·
        refine ⟨499376278178238299908142369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332917518785492199938761579 499376278178238299908142369)
        ·
          refine ⟨374532208633678724931106777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499376278178238299908142369 374532208633678724931106777)
          ·
            refine ⟨280899156475259043698330083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374532208633678724931106777 280899156475259043698330083)
            ·
              refine ⟨421348734712888565547495125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280899156475259043698330083 421348734712888565547495125)
              ·
                refine ⟨9875360969833325755019417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 421348734712888565547495125 9875360969833325755019417)
                ·
                  refine ⟨7406520727374994316264563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875360969833325755019417 7406520727374994316264563)
                  ·
                    refine ⟨11109781091062491474396845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7406520727374994316264563 11109781091062491474396845)
                    ·
                      refine ⟨4166167909148434302898817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11109781091062491474396845 4166167909148434302898817)
                      ·
                        rfl

theorem cell23_8113583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_8113583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113583 prefixEnd_8113583 := by exact prefixLift 8113583
  have htrace : WordTrace (prefixWord ++ tailWord_8113583) baseStart_8113583 baseEnd_8113583 := by
    simpa [prefixWord, tailWord_8113583, baseEnd_8113583] using wordTrace_append hprefix tailTrace_8113583
  have hstable : (prefixWord ++ tailWord_8113583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113583).length < 2 ^ (prefixWord ++ tailWord_8113583).sum := by decide
  have hdescent : baseEnd_8113583 < baseStart_8113583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113599 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 8]
def baseStart_8113599 : Nat := 118140960795 + 8113599 * 2 ^ 59
def prefixEnd_8113599 : Nat := 4983230072969 + 3 ^ 40 * 8113599 * 2
def baseEnd_8113599 : Nat := 1388725374946302080099581

theorem tailTrace_8113599 : CollatzResearch.WordTrace tailWord_8113599 prefixEnd_8113599 1388725374946302080099581 := by
  unfold tailWord_8113599
  simp only [CollatzResearch.WordTrace]
  refine ⟨295927266932823990233703851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197284844621882660155802567 295927266932823990233703851)
  ·
    refine ⟨443890900399235985350555777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295927266932823990233703851 443890900399235985350555777)
    ·
      refine ⟨332918175299426989012916833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443890900399235985350555777 332918175299426989012916833)
      ·
        refine ⟨249688631474570241759687625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332918175299426989012916833 249688631474570241759687625)
        ·
          refine ⟨187266473605927681319765719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249688631474570241759687625 187266473605927681319765719)
          ·
            refine ⟨280899710408891521979648579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187266473605927681319765719 280899710408891521979648579)
            ·
              refine ⟨421349565613337282969472869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280899710408891521979648579 421349565613337282969472869)
              ·
                refine ⟨79003043552500740556776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421349565613337282969472869 79003043552500740556776163)
                ·
                  refine ⟨118504565328751110835164245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79003043552500740556776163 118504565328751110835164245)
                  ·
                    refine ⟨1388725374946302080099581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118504565328751110835164245 1388725374946302080099581)
                    ·
                      rfl

theorem cell23_8113599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_8113599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113599 prefixEnd_8113599 := by exact prefixLift 8113599
  have htrace : WordTrace (prefixWord ++ tailWord_8113599) baseStart_8113599 baseEnd_8113599 := by
    simpa [prefixWord, tailWord_8113599, baseEnd_8113599] using wordTrace_append hprefix tailTrace_8113599
  have hstable : (prefixWord ++ tailWord_8113599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113599).length < 2 ^ (prefixWord ++ tailWord_8113599).sum := by decide
  have hdescent : baseEnd_8113599 < baseStart_8113599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113610 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_8113610 : Nat := 118140960795 + 8113610 * 2 ^ 59
def prefixEnd_8113610 : Nat := 4983230072969 + 3 ^ 40 * 8113610 * 2
def baseEnd_8113610 : Nat := 4166181773126105697261193

theorem tailTrace_8113610 : CollatzResearch.WordTrace tailWord_8113610 prefixEnd_8113610 4166181773126105697261193 := by
  unfold tailWord_8113610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73981917033946034778088571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197285112090522759408236189 73981917033946034778088571)
  ·
    refine ⟨110972875550919052167132857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73981917033946034778088571 110972875550919052167132857)
    ·
      refine ⟨83229656663189289125349643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110972875550919052167132857 83229656663189289125349643)
      ·
        refine ⟨124844484994783933688024465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83229656663189289125349643 124844484994783933688024465)
        ·
          refine ⟨93633363746087950266018349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124844484994783933688024465 93633363746087950266018349)
          ·
            refine ⟨35112511404782981349756881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93633363746087950266018349 35112511404782981349756881)
            ·
              refine ⟨26334383553587236012317661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35112511404782981349756881 26334383553587236012317661)
              ·
                refine ⟨9875393832595213504619123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26334383553587236012317661 9875393832595213504619123)
                ·
                  refine ⟨14813090748892820256928685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875393832595213504619123 14813090748892820256928685)
                  ·
                    refine ⟨5554909030834807596348257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14813090748892820256928685 5554909030834807596348257)
                    ·
                      refine ⟨4166181773126105697261193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5554909030834807596348257 4166181773126105697261193)
                      ·
                        rfl

theorem cell23_8113610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_8113610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113610 prefixEnd_8113610 := by exact prefixLift 8113610
  have htrace : WordTrace (prefixWord ++ tailWord_8113610) baseStart_8113610 baseEnd_8113610 := by
    simpa [prefixWord, tailWord_8113610, baseEnd_8113610] using wordTrace_append hprefix tailTrace_8113610
  have hstable : (prefixWord ++ tailWord_8113610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113610).length < 2 ^ (prefixWord ++ tailWord_8113610).sum := by decide
  have hdescent : baseEnd_8113610 < baseStart_8113610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8113636 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_8113636 : Nat := 118140960795 + 8113636 * 2 ^ 59
def prefixEnd_8113636 : Nat := 4983230072969 + 3 ^ 40 * 8113636 * 2
def baseEnd_8113636 : Nat := 4166195123623122595536073

theorem tailTrace_8113636 : CollatzResearch.WordTrace tailWord_8113636 prefixEnd_8113636 4166195123623122595536073 := by
  unfold tailWord_8113636
  simp only [CollatzResearch.WordTrace]
  refine ⟨147964308216844972776400381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197285744289126630368533841 147964308216844972776400381)
  ·
    refine ⟨55486615581316864791150143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147964308216844972776400381 55486615581316864791150143)
    ·
      refine ⟨83229923371975297186725215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55486615581316864791150143 83229923371975297186725215)
      ·
        refine ⟨124844885057962945780087823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83229923371975297186725215 124844885057962945780087823)
        ·
          refine ⟨187267327586944418670131735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124844885057962945780087823 187267327586944418670131735)
          ·
            refine ⟨280900991380416628005197603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187267327586944418670131735 280900991380416628005197603)
            ·
              refine ⟨421351487070624942007796405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280900991380416628005197603 421351487070624942007796405)
              ·
                refine ⟨39501701912871088313230913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 421351487070624942007796405 39501701912871088313230913)
                ·
                  refine ⟨29626276434653316234923185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39501701912871088313230913 29626276434653316234923185)
                  ·
                    refine ⟨22219707325989987176192389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29626276434653316234923185 22219707325989987176192389)
                    ·
                      refine ⟨4166195123623122595536073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22219707325989987176192389 4166195123623122595536073)
                      ·
                        rfl

theorem cell23_8113636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_8113636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8113636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8113636 prefixEnd_8113636 := by exact prefixLift 8113636
  have htrace : WordTrace (prefixWord ++ tailWord_8113636) baseStart_8113636 baseEnd_8113636 := by
    simpa [prefixWord, tailWord_8113636, baseEnd_8113636] using wordTrace_append hprefix tailTrace_8113636
  have hstable : (prefixWord ++ tailWord_8113636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8113636).length < 2 ^ (prefixWord ++ tailWord_8113636).sum := by decide
  have hdescent : baseEnd_8113636 < baseStart_8113636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8113636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
