import V185TrunkScan23Chunk0077

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_462737 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_462737 : Nat := 118140960795 + 462737 * 2 ^ 59
def prefixEnd_462737 : Nat := 4983230072969 + 3 ^ 40 * 462737 * 2
def baseEnd_462737 : Nat := 79202165873220424353139

theorem tailTrace_462737 : CollatzResearch.WordTrace tailWord_462737 prefixEnd_462737 79202165873220424353139 := by
  unfold tailWord_462737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877404924590353032874465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11251603283060235355249643 16877404924590353032874465)
  ·
    refine ⟨12658053693442764774655849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16877404924590353032874465 12658053693442764774655849)
    ·
      refine ⟨9493540270082073580991887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12658053693442764774655849 9493540270082073580991887)
      ·
        refine ⟨14240310405123110371487831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493540270082073580991887 14240310405123110371487831)
        ·
          refine ⟨21360465607684665557231747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14240310405123110371487831 21360465607684665557231747)
          ·
            refine ⟨32040698411526998335847621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21360465607684665557231747 32040698411526998335847621)
            ·
              refine ⟨6007630952161312187971429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32040698411526998335847621 6007630952161312187971429)
              ·
                refine ⟨1126430803530246035244643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6007630952161312187971429 1126430803530246035244643)
                ·
                  refine ⟨1689646205295369052866965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126430803530246035244643 1689646205295369052866965)
                  ·
                    refine ⟨79202165873220424353139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1689646205295369052866965 79202165873220424353139)
                    ·
                      rfl

theorem cell23_462737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_462737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462737 prefixEnd_462737 := by exact prefixLift 462737
  have htrace : WordTrace (prefixWord ++ tailWord_462737) baseStart_462737 baseEnd_462737 := by
    simpa [prefixWord, tailWord_462737, baseEnd_462737] using wordTrace_append hprefix tailTrace_462737
  have hstable : (prefixWord ++ tailWord_462737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462737).length < 2 ^ (prefixWord ++ tailWord_462737).sum := by decide
  have hdescent : baseEnd_462737 < baseStart_462737 := by decide
  rcases family_descends (prefixWord ++ tailWord_462737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462748 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_462748 : Nat := 118140960795 + 462748 * 2 ^ 59
def prefixEnd_462748 : Nat := 4983230072969 + 3 ^ 40 * 462748 * 2
def baseEnd_462748 : Nat := 237612145906860730021867

theorem tailTrace_462748 : CollatzResearch.WordTrace tailWord_462748 prefixEnd_462748 237612145906860730021867 := by
  unfold tailWord_462748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438903063775250955762449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11251870751700334607683265 8438903063775250955762449)
  ·
    refine ⟨6329177297831438216821837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8438903063775250955762449 6329177297831438216821837)
    ·
      refine ⟨2373441486686789331308189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6329177297831438216821837 2373441486686789331308189)
      ·
        refine ⟨890040557507545999240571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2373441486686789331308189 890040557507545999240571)
        ·
          refine ⟨1335060836261318998860857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890040557507545999240571 1335060836261318998860857)
          ·
            refine ⟨1001295627195989249145643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335060836261318998860857 1001295627195989249145643)
            ·
              refine ⟨1501943440793983873718465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001295627195989249145643 1501943440793983873718465)
              ·
                refine ⟨1126457580595487905288849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501943440793983873718465 1126457580595487905288849)
                ·
                  refine ⟨844843185446615928966637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1126457580595487905288849 844843185446615928966637)
                  ·
                    refine ⟨316816194542480973362489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844843185446615928966637 316816194542480973362489)
                    ·
                      refine ⟨237612145906860730021867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316816194542480973362489 237612145906860730021867)
                      ·
                        rfl

theorem cell23_462748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_462748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462748 prefixEnd_462748 := by exact prefixLift 462748
  have htrace : WordTrace (prefixWord ++ tailWord_462748) baseStart_462748 baseEnd_462748 := by
    simpa [prefixWord, tailWord_462748, baseEnd_462748] using wordTrace_append hprefix tailTrace_462748
  have hstable : (prefixWord ++ tailWord_462748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462748).length < 2 ^ (prefixWord ++ tailWord_462748).sum := by decide
  have hdescent : baseEnd_462748 < baseStart_462748 := by decide
  rcases family_descends (prefixWord ++ tailWord_462748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462761 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 3, 2, 2]
def baseStart_462761 : Nat := 118140960795 + 462761 * 2 ^ 59
def prefixEnd_462761 : Nat := 4983230072969 + 3 ^ 40 * 462761 * 2
def baseEnd_462761 : Nat := 237618821155369179159307

theorem tailTrace_462761 : CollatzResearch.WordTrace tailWord_462761 prefixEnd_462761 237618821155369179159307 := by
  unfold tailWord_462761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878280276503405131748137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11252186851002270087832091 16878280276503405131748137)
  ·
    refine ⟨12658710207377553848811103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16878280276503405131748137 12658710207377553848811103)
    ·
      refine ⟨18988065311066330773216655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12658710207377553848811103 18988065311066330773216655)
      ·
        refine ⟨28482097966599496159824983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18988065311066330773216655 28482097966599496159824983)
        ·
          refine ⟨42723146949899244239737475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28482097966599496159824983 42723146949899244239737475)
          ·
            refine ⟨64084720424848866359606213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42723146949899244239737475 64084720424848866359606213)
            ·
              refine ⟨12015885079659162442426165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64084720424848866359606213 12015885079659162442426165)
              ·
                refine ⟨1126489226218046478977453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12015885079659162442426165 1126489226218046478977453)
                ·
                  refine ⟨422433459831767429616545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126489226218046478977453 422433459831767429616545)
                  ·
                    refine ⟨316825094873825572212409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422433459831767429616545 316825094873825572212409)
                    ·
                      refine ⟨237618821155369179159307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316825094873825572212409 237618821155369179159307)
                      ·
                        rfl

theorem cell23_462761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2, 2].length) (baseStart_462761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462761 prefixEnd_462761 := by exact prefixLift 462761
  have htrace : WordTrace (prefixWord ++ tailWord_462761) baseStart_462761 baseEnd_462761 := by
    simpa [prefixWord, tailWord_462761, baseEnd_462761] using wordTrace_append hprefix tailTrace_462761
  have hstable : (prefixWord ++ tailWord_462761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462761).length < 2 ^ (prefixWord ++ tailWord_462761).sum := by decide
  have hdescent : baseEnd_462761 < baseStart_462761 := by decide
  rcases family_descends (prefixWord ++ tailWord_462761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462767 : List Nat := [1, 1, 2, 1, 2, 2, 6, 8]
def baseStart_462767 : Nat := 118140960795 + 462767 * 2 ^ 59
def prefixEnd_462767 : Nat := 4983230072969 + 3 ^ 40 * 462767 * 2
def baseEnd_462767 : Nat := 8800811186640598358677

theorem tailTrace_462767 : CollatzResearch.WordTrace tailWord_462767 prefixEnd_462767 8800811186640598358677 := by
  unfold tailWord_462767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16878499114481668156466555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11252332742987778770977703 16878499114481668156466555)
  ·
    refine ⟨25317748671722502234699833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16878499114481668156466555 25317748671722502234699833)
    ·
      refine ⟨18988311503791876676024875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25317748671722502234699833 18988311503791876676024875)
      ·
        refine ⟨28482467255687815014037313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18988311503791876676024875 28482467255687815014037313)
        ·
          refine ⟨21361850441765861260527985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28482467255687815014037313 21361850441765861260527985)
          ·
            refine ⟨16021387831324395945395989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21361850441765861260527985 16021387831324395945395989)
            ·
              refine ⟨751002554593331059940437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16021387831324395945395989 751002554593331059940437)
              ·
                refine ⟨8800811186640598358677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 751002554593331059940437 8800811186640598358677)
                ·
                  rfl

theorem cell23_462767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 8].length) (baseStart_462767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462767 prefixEnd_462767 := by exact prefixLift 462767
  have htrace : WordTrace (prefixWord ++ tailWord_462767) baseStart_462767 baseEnd_462767 := by
    simpa [prefixWord, tailWord_462767, baseEnd_462767] using wordTrace_append hprefix tailTrace_462767
  have hstable : (prefixWord ++ tailWord_462767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462767).length < 2 ^ (prefixWord ++ tailWord_462767).sum := by decide
  have hdescent : baseEnd_462767 < baseStart_462767 := by decide
  rcases family_descends (prefixWord ++ tailWord_462767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462781 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_462781 : Nat := 118140960795 + 462781 * 2 ^ 59
def prefixEnd_462781 : Nat := 4983230072969 + 3 ^ 40 * 462781 * 2
def baseEnd_462781 : Nat := 237629090768459100909215

theorem tailTrace_462781 : CollatzResearch.WordTrace tailWord_462781 prefixEnd_462781 237629090768459100909215 := by
  unfold tailWord_462781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879009736430948547476197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11252673157620632364984131 16879009736430948547476197)
  ·
    refine ⟨3164814325580802852651787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16879009736430948547476197 3164814325580802852651787)
    ·
      refine ⟨4747221488371204278977681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164814325580802852651787 4747221488371204278977681)
      ·
        refine ⟨3560416116278403209233261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4747221488371204278977681 3560416116278403209233261)
        ·
          refine ⟨1335156043604401203462473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3560416116278403209233261 1335156043604401203462473)
          ·
            refine ⟨1001367032703300902596855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335156043604401203462473 1001367032703300902596855)
            ·
              refine ⟨1502050549054951353895283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001367032703300902596855 1502050549054951353895283)
              ·
                refine ⟨2253075823582427030842925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502050549054951353895283 2253075823582427030842925)
                ·
                  refine ⟨844903433843410136566097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2253075823582427030842925 844903433843410136566097)
                  ·
                    refine ⟨633677575382557602424573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844903433843410136566097 633677575382557602424573)
                    ·
                      refine ⟨237629090768459100909215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633677575382557602424573 237629090768459100909215)
                      ·
                        rfl

theorem cell23_462781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_462781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462781 prefixEnd_462781 := by exact prefixLift 462781
  have htrace : WordTrace (prefixWord ++ tailWord_462781) baseStart_462781 baseEnd_462781 := by
    simpa [prefixWord, tailWord_462781, baseEnd_462781] using wordTrace_append hprefix tailTrace_462781
  have hstable : (prefixWord ++ tailWord_462781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462781).length < 2 ^ (prefixWord ++ tailWord_462781).sum := by decide
  have hdescent : baseEnd_462781 < baseStart_462781 := by decide
  rcases family_descends (prefixWord ++ tailWord_462781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462794 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_462794 : Nat := 118140960795 + 462794 * 2 ^ 59
def prefixEnd_462794 : Nat := 4983230072969 + 3 ^ 40 * 462794 * 2
def baseEnd_462794 : Nat := 237635766016967550046655

theorem tailTrace_462794 : CollatzResearch.WordTrace tailWord_462794 prefixEnd_462794 237635766016967550046655 := by
  unfold tailWord_462794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219870971345962941924859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11252989256922567845132957 4219870971345962941924859)
  ·
    refine ⟨6329806457018944412887289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219870971345962941924859 6329806457018944412887289)
    ·
      refine ⟨4747354842764208309665467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6329806457018944412887289 4747354842764208309665467)
      ·
        refine ⟨7121032264146312464498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747354842764208309665467 7121032264146312464498201)
        ·
          refine ⟨5340774198109734348373651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121032264146312464498201 5340774198109734348373651)
          ·
            refine ⟨8011161297164601522560477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340774198109734348373651 8011161297164601522560477)
            ·
              refine ⟨3004185486436725570960179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8011161297164601522560477 3004185486436725570960179)
              ·
                refine ⟨4506278229655088356440269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004185486436725570960179 4506278229655088356440269)
                ·
                  refine ⟨1689854336120658133665101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4506278229655088356440269 1689854336120658133665101)
                  ·
                    refine ⟨633695376045246800124413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689854336120658133665101 633695376045246800124413)
                    ·
                      refine ⟨237635766016967550046655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633695376045246800124413 237635766016967550046655)
                      ·
                        rfl

theorem cell23_462794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_462794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462794 prefixEnd_462794 := by exact prefixLift 462794
  have htrace : WordTrace (prefixWord ++ tailWord_462794) baseStart_462794 baseEnd_462794 := by
    simpa [prefixWord, tailWord_462794, baseEnd_462794] using wordTrace_append hprefix tailTrace_462794
  have hstable : (prefixWord ++ tailWord_462794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462794).length < 2 ^ (prefixWord ++ tailWord_462794).sum := by decide
  have hdescent : baseEnd_462794 < baseStart_462794 := by decide
  rcases family_descends (prefixWord ++ tailWord_462794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462798 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_462798 : Nat := 118140960795 + 462798 * 2 ^ 59
def prefixEnd_462798 : Nat := 4983230072969 + 3 ^ 40 * 462798 * 2
def baseEnd_462798 : Nat := 237637819939585534396637

theorem tailTrace_462798 : CollatzResearch.WordTrace tailWord_462798 prefixEnd_462798 237637819939585534396637 := by
  unfold tailWord_462798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109953722171170056355631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11253086518246240300563365 2109953722171170056355631)
  ·
    refine ⟨3164930583256755084533447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2109953722171170056355631 3164930583256755084533447)
    ·
      refine ⟨4747395874885132626800171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164930583256755084533447 4747395874885132626800171)
      ·
        refine ⟨7121093812327698940200257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747395874885132626800171 7121093812327698940200257)
        ·
          refine ⟨5340820359245774205150193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121093812327698940200257 5340820359245774205150193)
          ·
            refine ⟨4005615269434330653862645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340820359245774205150193 4005615269434330653862645)
            ·
              refine ⟨375526431509468498799623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4005615269434330653862645 375526431509468498799623)
              ·
                refine ⟨563289647264202748199435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375526431509468498799623 563289647264202748199435)
                ·
                  refine ⟨844934470896304122299153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563289647264202748199435 844934470896304122299153)
                  ·
                    refine ⟨633700853172228091724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844934470896304122299153 633700853172228091724365)
                    ·
                      refine ⟨237637819939585534396637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633700853172228091724365 237637819939585534396637)
                      ·
                        rfl

theorem cell23_462798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_462798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462798 prefixEnd_462798 := by exact prefixLift 462798
  have htrace : WordTrace (prefixWord ++ tailWord_462798) baseStart_462798 baseEnd_462798 := by
    simpa [prefixWord, tailWord_462798, baseEnd_462798] using wordTrace_append hprefix tailTrace_462798
  have hstable : (prefixWord ++ tailWord_462798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462798).length < 2 ^ (prefixWord ++ tailWord_462798).sum := by decide
  have hdescent : baseEnd_462798 < baseStart_462798 := by decide
  rcases family_descends (prefixWord ++ tailWord_462798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462806 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_462806 : Nat := 118140960795 + 462806 * 2 ^ 59
def prefixEnd_462806 : Nat := 4983230072969 + 3 ^ 40 * 462806 * 2
def baseEnd_462806 : Nat := 237641927784821503096601

theorem tailTrace_462806 : CollatzResearch.WordTrace tailWord_462806 prefixEnd_462806 237641927784821503096601 := by
  unfold tailWord_462806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054995097583773613571017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11253281040893585211424181 1054995097583773613571017)
  ·
    refine ⟨791246323187830210178263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1054995097583773613571017 791246323187830210178263)
    ·
      refine ⟨1186869484781745315267395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791246323187830210178263 1186869484781745315267395)
      ·
        refine ⟨1780304227172617972901093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186869484781745315267395 1780304227172617972901093)
        ·
          refine ⟨333807042594865869918955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1780304227172617972901093 333807042594865869918955)
          ·
            refine ⟨500710563892298804878433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333807042594865869918955 500710563892298804878433)
            ·
              refine ⟨375532922919224103658825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500710563892298804878433 375532922919224103658825)
              ·
                refine ⟨281649692189418077744119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375532922919224103658825 281649692189418077744119)
                ·
                  refine ⟨422474538284127116616179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281649692189418077744119 422474538284127116616179)
                  ·
                    refine ⟨633711807426190674924269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422474538284127116616179 633711807426190674924269)
                    ·
                      refine ⟨237641927784821503096601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633711807426190674924269 237641927784821503096601)
                      ·
                        rfl

theorem cell23_462806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_462806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462806 prefixEnd_462806 := by exact prefixLift 462806
  have htrace : WordTrace (prefixWord ++ tailWord_462806) baseStart_462806 baseEnd_462806 := by
    simpa [prefixWord, tailWord_462806, baseEnd_462806] using wordTrace_append hprefix tailTrace_462806
  have hstable : (prefixWord ++ tailWord_462806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462806).length < 2 ^ (prefixWord ++ tailWord_462806).sum := by decide
  have hdescent : baseEnd_462806 < baseStart_462806 := by decide
  rcases family_descends (prefixWord ++ tailWord_462806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462818 : List Nat := [3, 3, 3, 1, 2, 2, 1, 8]
def baseStart_462818 : Nat := 118140960795 + 462818 * 2 ^ 59
def prefixEnd_462818 : Nat := 4983230072969 + 3 ^ 40 * 462818 * 2
def baseEnd_462818 : Nat := 8801781094543535412835

theorem tailTrace_462818 : CollatzResearch.WordTrace tailWord_462818 prefixEnd_462818 8801781094543535412835 := by
  unfold tailWord_462818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220089809324225966643277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11253572824864602577715405 4220089809324225966643277)
  ·
    refine ⟨1582533678496584737491229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4220089809324225966643277 1582533678496584737491229)
    ·
      refine ⟨593450129436219276559211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1582533678496584737491229 593450129436219276559211)
      ·
        refine ⟨890175194154328914838817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593450129436219276559211 890175194154328914838817)
        ·
          refine ⟨667631395615746686129113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890175194154328914838817 667631395615746686129113)
          ·
            refine ⟨500723546711810014596835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667631395615746686129113 500723546711810014596835)
            ·
              refine ⟨751085320067715021895253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500723546711810014596835 751085320067715021895253)
              ·
                refine ⟨8801781094543535412835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 751085320067715021895253 8801781094543535412835)
                ·
                  rfl

theorem cell23_462818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_462818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462818 prefixEnd_462818 := by exact prefixLift 462818
  have htrace : WordTrace (prefixWord ++ tailWord_462818) baseStart_462818 baseEnd_462818 := by
    simpa [prefixWord, tailWord_462818, baseEnd_462818] using wordTrace_append hprefix tailTrace_462818
  have hstable : (prefixWord ++ tailWord_462818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462818).length < 2 ^ (prefixWord ++ tailWord_462818).sum := by decide
  have hdescent : baseEnd_462818 < baseStart_462818 := by decide
  rcases family_descends (prefixWord ++ tailWord_462818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462855 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_462855 : Nat := 118140960795 + 462855 * 2 ^ 59
def prefixEnd_462855 : Nat := 4983230072969 + 3 ^ 40 * 462855 * 2
def baseEnd_462855 : Nat := 237667088336891811383875

theorem tailTrace_462855 : CollatzResearch.WordTrace tailWord_462855 prefixEnd_462855 237667088336891811383875 := by
  unfold tailWord_462855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881708738162859185670019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11254472492108572790446679 16881708738162859185670019)
  ·
    refine ⟨25322563107244288778505029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16881708738162859185670019 25322563107244288778505029)
    ·
      refine ⟨4747980582608304145969693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25322563107244288778505029 4747980582608304145969693)
      ·
        refine ⟨1780492718478114054738635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4747980582608304145969693 1780492718478114054738635)
        ·
          refine ⟨2670739077717171082107953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780492718478114054738635 2670739077717171082107953)
          ·
            refine ⟨2003054308287878311580965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670739077717171082107953 2003054308287878311580965)
            ·
              refine ⟨375572682803977183421431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2003054308287878311580965 375572682803977183421431)
              ·
                refine ⟨563359024205965775132147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375572682803977183421431 563359024205965775132147)
                ·
                  refine ⟨845038536308948662698221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563359024205965775132147 845038536308948662698221)
                  ·
                    refine ⟨316889451115855748511833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845038536308948662698221 316889451115855748511833)
                    ·
                      refine ⟨237667088336891811383875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 316889451115855748511833 237667088336891811383875)
                      ·
                        rfl

theorem cell23_462855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_462855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462855 prefixEnd_462855 := by exact prefixLift 462855
  have htrace : WordTrace (prefixWord ++ tailWord_462855) baseStart_462855 baseEnd_462855 := by
    simpa [prefixWord, tailWord_462855, baseEnd_462855] using wordTrace_append hprefix tailTrace_462855
  have hstable : (prefixWord ++ tailWord_462855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462855).length < 2 ^ (prefixWord ++ tailWord_462855).sum := by decide
  have hdescent : baseEnd_462855 < baseStart_462855 := by decide
  rcases family_descends (prefixWord ++ tailWord_462855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462874 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_462874 : Nat := 118140960795 + 462874 * 2 ^ 59
def prefixEnd_462874 : Nat := 4983230072969 + 3 ^ 40 * 462874 * 2
def baseEnd_462874 : Nat := 26408538274369693005143

theorem tailTrace_462874 : CollatzResearch.WordTrace tailWord_462874 prefixEnd_462874 26408538274369693005143 := by
  unfold tailWord_462874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220600431273506357652919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11254934483396016953741117 4220600431273506357652919)
  ·
    refine ⟨6330900646910259536479379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4220600431273506357652919 6330900646910259536479379)
    ·
      refine ⟨9496350970365389304719069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330900646910259536479379 9496350970365389304719069)
      ·
        refine ⟨3561131613887020989269651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9496350970365389304719069 3561131613887020989269651)
        ·
          refine ⟨5341697420830531483904477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561131613887020989269651 5341697420830531483904477)
          ·
            refine ⟨2003136532811449306464179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5341697420830531483904477 2003136532811449306464179)
            ·
              refine ⟨3004704799217173959696269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003136532811449306464179 3004704799217173959696269)
              ·
                refine ⟨1126764299706440234886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004704799217173959696269 1126764299706440234886101)
                ·
                  refine ⟨26408538274369693005143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1126764299706440234886101 26408538274369693005143)
                  ·
                    rfl

theorem cell23_462874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_462874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462874 prefixEnd_462874 := by exact prefixLift 462874
  have htrace : WordTrace (prefixWord ++ tailWord_462874) baseStart_462874 baseEnd_462874 := by
    simpa [prefixWord, tailWord_462874, baseEnd_462874] using wordTrace_append hprefix tailTrace_462874
  have hstable : (prefixWord ++ tailWord_462874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462874).length < 2 ^ (prefixWord ++ tailWord_462874).sum := by decide
  have hdescent : baseEnd_462874 < baseStart_462874 := by decide
  rcases family_descends (prefixWord ++ tailWord_462874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462925 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 5]
def baseStart_462925 : Nat := 118140960795 + 462925 * 2 ^ 59
def prefixEnd_462925 : Nat := 4983230072969 + 3 ^ 40 * 462925 * 2
def baseEnd_462925 : Nat := 26411447998078504167617

theorem tailTrace_462925 : CollatzResearch.WordTrace tailWord_462925 prefixEnd_462925 26411447998078504167617 := by
  unfold tailWord_462925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884261847909261140718229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11256174565272840760478819 16884261847909261140718229)
  ·
    refine ⟨791449774120746615971167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16884261847909261140718229 791449774120746615971167)
    ·
      refine ⟨1187174661181119923956751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791449774120746615971167 1187174661181119923956751)
      ·
        refine ⟨1780761991771679885935127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187174661181119923956751 1780761991771679885935127)
        ·
          refine ⟨2671142987657519828902691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780761991771679885935127 2671142987657519828902691)
          ·
            refine ⟨4006714481486279743354037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671142987657519828902691 4006714481486279743354037)
            ·
              refine ⟨375629482639338725939441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4006714481486279743354037 375629482639338725939441)
              ·
                refine ⟨281722111979504044454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375629482639338725939441 281722111979504044454581)
                ·
                  refine ⟨26411447998078504167617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281722111979504044454581 26411447998078504167617)
                  ·
                    rfl

theorem cell23_462925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_462925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462925 prefixEnd_462925 := by exact prefixLift 462925
  have htrace : WordTrace (prefixWord ++ tailWord_462925) baseStart_462925 baseEnd_462925 := by
    simpa [prefixWord, tailWord_462925, baseEnd_462925] using wordTrace_append hprefix tailTrace_462925
  have hstable : (prefixWord ++ tailWord_462925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462925).length < 2 ^ (prefixWord ++ tailWord_462925).sum := by decide
  have hdescent : baseEnd_462925 < baseStart_462925 := by decide
  rcases family_descends (prefixWord ++ tailWord_462925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462951 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 5, 4]
def baseStart_462951 : Nat := 118140960795 + 462951 * 2 ^ 59
def prefixEnd_462951 : Nat := 4983230072969 + 3 ^ 40 * 462951 * 2
def baseEnd_462951 : Nat := 79238794159907811927811

theorem tailTrace_462951 : CollatzResearch.WordTrace tailWord_462951 prefixEnd_462951 79238794159907811927811 := by
  unfold tailWord_462951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16885210145815067581164707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11256806763876711720776471 16885210145815067581164707)
  ·
    refine ⟨25327815218722601371747061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16885210145815067581164707 25327815218722601371747061)
    ·
      refine ⟨2374482676755243878601287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25327815218722601371747061 2374482676755243878601287)
      ·
        refine ⟨3561724015132865817901931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374482676755243878601287 3561724015132865817901931)
        ·
          refine ⟨5342586022699298726852897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561724015132865817901931 5342586022699298726852897)
          ·
            refine ⟨4006939517024474045139673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342586022699298726852897 4006939517024474045139673)
            ·
              refine ⟨3005204637768355533854755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006939517024474045139673 3005204637768355533854755)
              ·
                refine ⟨4507806956652533300782133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005204637768355533854755 4507806956652533300782133)
                ·
                  refine ⟨422606902186174996948325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4507806956652533300782133 422606902186174996948325)
                  ·
                    refine ⟨79238794159907811927811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422606902186174996948325 79238794159907811927811)
                    ·
                      rfl

theorem cell23_462951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_462951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462951 prefixEnd_462951 := by exact prefixLift 462951
  have htrace : WordTrace (prefixWord ++ tailWord_462951) baseStart_462951 baseEnd_462951 := by
    simpa [prefixWord, tailWord_462951, baseEnd_462951] using wordTrace_append hprefix tailTrace_462951
  have hstable : (prefixWord ++ tailWord_462951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462951).length < 2 ^ (prefixWord ++ tailWord_462951).sum := by decide
  have hdescent : baseEnd_462951 < baseStart_462951 := by decide
  rcases family_descends (prefixWord ++ tailWord_462951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462958 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_462958 : Nat := 118140960795 + 462958 * 2 ^ 59
def prefixEnd_462958 : Nat := 4983230072969 + 3 ^ 40 * 462958 * 2
def baseEnd_462958 : Nat := 237719976844304908395901

theorem tailTrace_462958 : CollatzResearch.WordTrace tailWord_462958 prefixEnd_462958 237719976844304908395901 := by
  unfold tailWord_462958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110683182098713472083691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11256976971193138517779685 2110683182098713472083691)
  ·
    refine ⟨3166024773148070208125537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110683182098713472083691 3166024773148070208125537)
    ·
      refine ⟨2374518579861052656094153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3166024773148070208125537 2374518579861052656094153)
      ·
        refine ⟨1780888934895789492070615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2374518579861052656094153 1780888934895789492070615)
        ·
          refine ⟨2671333402343684238105923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780888934895789492070615 2671333402343684238105923)
          ·
            refine ⟨4007000103515526357158885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671333402343684238105923 4007000103515526357158885)
            ·
              refine ⟨751312519409161191967291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4007000103515526357158885 751312519409161191967291)
              ·
                refine ⟨1126968779113741787950937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751312519409161191967291 1126968779113741787950937)
                ·
                  refine ⟨845226584335306340963203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1126968779113741787950937 845226584335306340963203)
                  ·
                    refine ⟨1267839876502959511444805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845226584335306340963203 1267839876502959511444805)
                    ·
                      refine ⟨237719976844304908395901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1267839876502959511444805 237719976844304908395901)
                      ·
                        rfl

theorem cell23_462958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_462958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462958 prefixEnd_462958 := by exact prefixLift 462958
  have htrace : WordTrace (prefixWord ++ tailWord_462958) baseStart_462958 baseEnd_462958 := by
    simpa [prefixWord, tailWord_462958, baseEnd_462958] using wordTrace_append hprefix tailTrace_462958
  have hstable : (prefixWord ++ tailWord_462958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462958).length < 2 ^ (prefixWord ++ tailWord_462958).sum := by decide
  have hdescent : baseEnd_462958 < baseStart_462958 := by decide
  rcases family_descends (prefixWord ++ tailWord_462958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462968 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 1, 4]
def baseStart_462968 : Nat := 118140960795 + 462968 * 2 ^ 59
def prefixEnd_462968 : Nat := 4983230072969 + 3 ^ 40 * 462968 * 2
def baseEnd_462968 : Nat := 79241703883616623090285

theorem tailTrace_462968 : CollatzResearch.WordTrace tailWord_462968 prefixEnd_462968 79241703883616623090285 := by
  unfold tailWord_462968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442915093376739742266779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11257220124502319656355705 8442915093376739742266779)
  ·
    refine ⟨12664372640065109613400169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8442915093376739742266779 12664372640065109613400169)
    ·
      refine ⟨9498279480048832210050127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12664372640065109613400169 9498279480048832210050127)
      ·
        refine ⟨14247419220073248315075191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498279480048832210050127 14247419220073248315075191)
        ·
          refine ⟨21371128830109872472612787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14247419220073248315075191 21371128830109872472612787)
          ·
            refine ⟨32056693245164808708919181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21371128830109872472612787 32056693245164808708919181)
            ·
              refine ⟨12021259966936803265844693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32056693245164808708919181 12021259966936803265844693)
              ·
                refine ⟨281748280475081326543235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12021259966936803265844693 281748280475081326543235)
                ·
                  refine ⟨422622420712621989814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281748280475081326543235 422622420712621989814853)
                  ·
                    refine ⟨79241703883616623090285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422622420712621989814853 79241703883616623090285)
                    ·
                      rfl

theorem cell23_462968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_462968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462968 prefixEnd_462968 := by exact prefixLift 462968
  have htrace : WordTrace (prefixWord ++ tailWord_462968) baseStart_462968 baseEnd_462968 := by
    simpa [prefixWord, tailWord_462968, baseEnd_462968] using wordTrace_append hprefix tailTrace_462968
  have hstable : (prefixWord ++ tailWord_462968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462968).length < 2 ^ (prefixWord ++ tailWord_462968).sum := by decide
  have hdescent : baseEnd_462968 < baseStart_462968 := by decide
  rcases family_descends (prefixWord ++ tailWord_462968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462981 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 6]
def baseStart_462981 : Nat := 118140960795 + 462981 * 2 ^ 59
def prefixEnd_462981 : Nat := 4983230072969 + 3 ^ 40 * 462981 * 2
def baseEnd_462981 : Nat := 26414642988817590934255

theorem tailTrace_462981 : CollatzResearch.WordTrace tailWord_462981 prefixEnd_462981 26414642988817590934255 := by
  unfold tailWord_462981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16886304335706382704756797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11257536223804255136504531 16886304335706382704756797)
  ·
    refine ⟨6332364125889893514283799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16886304335706382704756797 6332364125889893514283799)
    ·
      refine ⟨9498546188834840271425699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332364125889893514283799 9498546188834840271425699)
      ·
        refine ⟨14247819283252260407138549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9498546188834840271425699 14247819283252260407138549)
        ·
          refine ⟨1335733057804899413169239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14247819283252260407138549 1335733057804899413169239)
          ·
            refine ⟨2003599586707349119753859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335733057804899413169239 2003599586707349119753859)
            ·
              refine ⟨3005399380061023679630789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003599586707349119753859 3005399380061023679630789)
              ·
                refine ⟨563512383761441939930773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3005399380061023679630789 563512383761441939930773)
                ·
                  refine ⟨26414642988817590934255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 563512383761441939930773 26414642988817590934255)
                  ·
                    rfl

theorem cell23_462981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_462981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_462981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_462981 prefixEnd_462981 := by exact prefixLift 462981
  have htrace : WordTrace (prefixWord ++ tailWord_462981) baseStart_462981 baseEnd_462981 := by
    simpa [prefixWord, tailWord_462981, baseEnd_462981] using wordTrace_append hprefix tailTrace_462981
  have hstable : (prefixWord ++ tailWord_462981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462981).length < 2 ^ (prefixWord ++ tailWord_462981).sum := by decide
  have hdescent : baseEnd_462981 < baseStart_462981 := by decide
  rcases family_descends (prefixWord ++ tailWord_462981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463008 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_463008 : Nat := 118140960795 + 463008 * 2 ^ 59
def prefixEnd_463008 : Nat := 4983230072969 + 3 ^ 40 * 463008 * 2
def baseEnd_463008 : Nat := 237745650877029712770671

theorem tailTrace_463008 : CollatzResearch.WordTrace tailWord_463008 prefixEnd_463008 237745650877029712770671 := by
  unfold tailWord_463008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443644553304283157994839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11258192737739044210659785 8443644553304283157994839)
  ·
    refine ⟨12665466829956424736992259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443644553304283157994839 12665466829956424736992259)
    ·
      refine ⟨18998200244934637105488389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12665466829956424736992259 18998200244934637105488389)
      ·
        refine ⟨3562162545925244457279073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18998200244934637105488389 3562162545925244457279073)
        ·
          refine ⟨2671621909443933342959305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562162545925244457279073 2671621909443933342959305)
          ·
            refine ⟨2003716432082950007219479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2671621909443933342959305 2003716432082950007219479)
            ·
              refine ⟨3005574648124425010829219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003716432082950007219479 3005574648124425010829219)
              ·
                refine ⟨4508361972186637516243829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005574648124425010829219 4508361972186637516243829)
                ·
                  refine ⟨422658934892497267147859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4508361972186637516243829 422658934892497267147859)
                  ·
                    refine ⟨633988402338745900721789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422658934892497267147859 633988402338745900721789)
                    ·
                      refine ⟨237745650877029712770671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633988402338745900721789 237745650877029712770671)
                      ·
                        rfl

theorem cell23_463008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_463008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463008 prefixEnd_463008 := by exact prefixLift 463008
  have htrace : WordTrace (prefixWord ++ tailWord_463008) baseStart_463008 baseEnd_463008 := by
    simpa [prefixWord, tailWord_463008, baseEnd_463008] using wordTrace_append hprefix tailTrace_463008
  have hstable : (prefixWord ++ tailWord_463008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463008).length < 2 ^ (prefixWord ++ tailWord_463008).sum := by decide
  have hdescent : baseEnd_463008 < baseStart_463008 := by decide
  rcases family_descends (prefixWord ++ tailWord_463008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463012 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_463012 : Nat := 118140960795 + 463012 * 2 ^ 59
def prefixEnd_463012 : Nat := 4983230072969 + 3 ^ 40 * 463012 * 2
def baseEnd_463012 : Nat := 237747704799647697120653

theorem tailTrace_463012 : CollatzResearch.WordTrace tailWord_463012 prefixEnd_463012 237747704799647697120653 := by
  unfold tailWord_463012
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443717499297037499567645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11258289999062716666090193 8443717499297037499567645)
  ·
    refine ⟨3166394062236389062337867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8443717499297037499567645 3166394062236389062337867)
    ·
      refine ⟨4749591093354583593506801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166394062236389062337867 4749591093354583593506801)
      ·
        refine ⟨3562193320015937695130101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4749591093354583593506801 3562193320015937695130101)
        ·
          refine ⟨333955623751494158918447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3562193320015937695130101 333955623751494158918447)
          ·
            refine ⟨500933435627241238377671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333955623751494158918447 500933435627241238377671)
            ·
              refine ⟨751400153440861857566507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500933435627241238377671 751400153440861857566507)
              ·
                refine ⟨1127100230161292786349761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751400153440861857566507 1127100230161292786349761)
                ·
                  refine ⟨845325172620969589762321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1127100230161292786349761 845325172620969589762321)
                  ·
                    refine ⟨633993879465727192321741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 845325172620969589762321 633993879465727192321741)
                    ·
                      refine ⟨237747704799647697120653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 633993879465727192321741 237747704799647697120653)
                      ·
                        rfl

theorem cell23_463012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_463012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463012 prefixEnd_463012 := by exact prefixLift 463012
  have htrace : WordTrace (prefixWord ++ tailWord_463012) baseStart_463012 baseEnd_463012 := by
    simpa [prefixWord, tailWord_463012, baseEnd_463012] using wordTrace_append hprefix tailTrace_463012
  have hstable : (prefixWord ++ tailWord_463012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463012).length < 2 ^ (prefixWord ++ tailWord_463012).sum := by decide
  have hdescent : baseEnd_463012 < baseStart_463012 := by decide
  rcases family_descends (prefixWord ++ tailWord_463012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463051 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5]
def baseStart_463051 : Nat := 118140960795 + 463051 * 2 ^ 59
def prefixEnd_463051 : Nat := 4983230072969 + 3 ^ 40 * 463051 * 2
def baseEnd_463051 : Nat := 237767730545173044532973

theorem tailTrace_463051 : CollatzResearch.WordTrace tailWord_463051 prefixEnd_463051 237767730545173044532973 := by
  unfold tailWord_463051
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888857445452784659805007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259238296968523106536671 16888857445452784659805007)
  ·
    refine ⟨25333286168179176989707511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888857445452784659805007 25333286168179176989707511)
    ·
      refine ⟨37999929252268765484561267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333286168179176989707511 37999929252268765484561267)
      ·
        refine ⟨56999893878403148226841901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37999929252268765484561267 56999893878403148226841901)
        ·
          refine ⟨21374960204401180585065713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56999893878403148226841901 21374960204401180585065713)
          ·
            refine ⟨16031220153300885438799285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21374960204401180585065713 16031220153300885438799285)
            ·
              refine ⟨1502926889371958009887433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16031220153300885438799285 1502926889371958009887433)
              ·
                refine ⟨1127195167028968507415575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502926889371958009887433 1127195167028968507415575)
                ·
                  refine ⟨1690792750543452761123363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127195167028968507415575 1690792750543452761123363)
                  ·
                    refine ⟨2536189125815179141685045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690792750543452761123363 2536189125815179141685045)
                    ·
                      refine ⟨237767730545173044532973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2536189125815179141685045 237767730545173044532973)
                      ·
                        rfl

theorem cell23_463051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_463051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463051 prefixEnd_463051 := by exact prefixLift 463051
  have htrace : WordTrace (prefixWord ++ tailWord_463051) baseStart_463051 baseEnd_463051 := by
    simpa [prefixWord, tailWord_463051, baseEnd_463051] using wordTrace_append hprefix tailTrace_463051
  have hstable : (prefixWord ++ tailWord_463051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463051).length < 2 ^ (prefixWord ++ tailWord_463051).sum := by decide
  have hdescent : baseEnd_463051 < baseStart_463051 := by decide
  rcases family_descends (prefixWord ++ tailWord_463051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463058 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_463058 : Nat := 118140960795 + 463058 * 2 ^ 59
def prefixEnd_463058 : Nat := 4983230072969 + 3 ^ 40 * 463058 * 2
def baseEnd_463058 : Nat := 79257108303251505715147

theorem tailTrace_463058 : CollatzResearch.WordTrace tailWord_463058 prefixEnd_463058 79257108303251505715147 := by
  unfold tailWord_463058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222278189106856213827457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11259408504284949903539885 4222278189106856213827457)
  ·
    refine ⟨3166708641830142160370593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4222278189106856213827457 3166708641830142160370593)
    ·
      refine ⟨2375031481372606620277945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3166708641830142160370593 2375031481372606620277945)
      ·
        refine ⟨1781273611029454965208459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375031481372606620277945 1781273611029454965208459)
        ·
          refine ⟨2671910416544182447812689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781273611029454965208459 2671910416544182447812689)
          ·
            refine ⟨2003932812408136835859517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2671910416544182447812689 2003932812408136835859517)
            ·
              refine ⟨751474804653051313447319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2003932812408136835859517 751474804653051313447319)
              ·
                refine ⟨1127212206979576970170979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751474804653051313447319 1127212206979576970170979)
                ·
                  refine ⟨1690818310469365455256469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127212206979576970170979 1690818310469365455256469)
                  ·
                    refine ⟨79257108303251505715147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1690818310469365455256469 79257108303251505715147)
                    ·
                      rfl

theorem cell23_463058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_463058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463058 prefixEnd_463058 := by exact prefixLift 463058
  have htrace : WordTrace (prefixWord ++ tailWord_463058) baseStart_463058 baseEnd_463058 := by
    simpa [prefixWord, tailWord_463058, baseEnd_463058] using wordTrace_append hprefix tailTrace_463058
  have hstable : (prefixWord ++ tailWord_463058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463058).length < 2 ^ (prefixWord ++ tailWord_463058).sum := by decide
  have hdescent : baseEnd_463058 < baseStart_463058 := by decide
  rcases family_descends (prefixWord ++ tailWord_463058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463062 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_463062 : Nat := 118140960795 + 463062 * 2 ^ 59
def prefixEnd_463062 : Nat := 4983230072969 + 3 ^ 40 * 463062 * 2
def baseEnd_463062 : Nat := 79257792944124167165141

theorem tailTrace_463062 : CollatzResearch.WordTrace tailWord_463062 prefixEnd_463062 79257792944124167165141 := by
  unfold tailWord_463062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055578665525808346153465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11259505765608622358970293 1055578665525808346153465)
  ·
    refine ⟨791683999144356259615099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055578665525808346153465 791683999144356259615099)
    ·
      refine ⟨1187525998716534389422649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791683999144356259615099 1187525998716534389422649)
      ·
        refine ⟨890644499037400792066987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187525998716534389422649 890644499037400792066987)
        ·
          refine ⟨1335966748556101188100481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890644499037400792066987 1335966748556101188100481)
          ·
            refine ⟨1001975061417075891075361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335966748556101188100481 1001975061417075891075361)
            ·
              refine ⟨751481296062806918306521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001975061417075891075361 751481296062806918306521)
              ·
                refine ⟨563610972047105188729891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751481296062806918306521 563610972047105188729891)
                ·
                  refine ⟨845416458070657783094837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563610972047105188729891 845416458070657783094837)
                  ·
                    refine ⟨79257792944124167165141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 845416458070657783094837 79257792944124167165141)
                    ·
                      rfl

theorem cell23_463062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_463062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463062 prefixEnd_463062 := by exact prefixLift 463062
  have htrace : WordTrace (prefixWord ++ tailWord_463062) baseStart_463062 baseEnd_463062 := by
    simpa [prefixWord, tailWord_463062, baseEnd_463062] using wordTrace_append hprefix tailTrace_463062
  have hstable : (prefixWord ++ tailWord_463062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463062).length < 2 ^ (prefixWord ++ tailWord_463062).sum := by decide
  have hdescent : baseEnd_463062 < baseStart_463062 := by decide
  rcases family_descends (prefixWord ++ tailWord_463062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463065 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 3, 2, 2]
def baseStart_463065 : Nat := 118140960795 + 463065 * 2 ^ 59
def prefixEnd_463065 : Nat := 4983230072969 + 3 ^ 40 * 463065 * 2
def baseEnd_463065 : Nat := 237774919274335989757909

theorem tailTrace_463065 : CollatzResearch.WordTrace tailWord_463065 prefixEnd_463065 237774919274335989757909 := by
  unfold tailWord_463065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889368067402065050814649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259578711601376700543099 16889368067402065050814649)
  ·
    refine ⟨12667026050551548788110987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16889368067402065050814649 12667026050551548788110987)
    ·
      refine ⟨19000539075827323182166481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12667026050551548788110987 19000539075827323182166481)
      ·
        refine ⟨14250404306870492386624861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19000539075827323182166481 14250404306870492386624861)
        ·
          refine ⟨5343901615076434644984323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14250404306870492386624861 5343901615076434644984323)
          ·
            refine ⟨8015852422614651967476485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343901615076434644984323 8015852422614651967476485)
            ·
              refine ⟨1502972329240247243901841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8015852422614651967476485 1502972329240247243901841)
              ·
                refine ⟨1127229246930185432926381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502972329240247243901841 1127229246930185432926381)
                ·
                  refine ⟨422710967598819537347393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127229246930185432926381 422710967598819537347393)
                  ·
                    refine ⟨317033225699114653010545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422710967598819537347393 317033225699114653010545)
                    ·
                      refine ⟨237774919274335989757909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317033225699114653010545 237774919274335989757909)
                      ·
                        rfl

theorem cell23_463065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_463065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463065 prefixEnd_463065 := by exact prefixLift 463065
  have htrace : WordTrace (prefixWord ++ tailWord_463065) baseStart_463065 baseEnd_463065 := by
    simpa [prefixWord, tailWord_463065, baseEnd_463065] using wordTrace_append hprefix tailTrace_463065
  have hstable : (prefixWord ++ tailWord_463065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463065).length < 2 ^ (prefixWord ++ tailWord_463065).sum := by decide
  have hdescent : baseEnd_463065 < baseStart_463065 := by decide
  rcases family_descends (prefixWord ++ tailWord_463065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463085 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_463085 : Nat := 118140960795 + 463085 * 2 ^ 59
def prefixEnd_463085 : Nat := 4983230072969 + 3 ^ 40 * 463085 * 2
def baseEnd_463085 : Nat := 237785188887425911507817

theorem tailTrace_463085 : CollatzResearch.WordTrace tailWord_463085 prefixEnd_463085 237785188887425911507817 := by
  unfold tailWord_463085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16890097527329608466542709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11260065018219738977695139 16890097527329608466542709)
  ·
    refine ⟨1583446643187150793738379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16890097527329608466542709 1583446643187150793738379)
    ·
      refine ⟨2375169964780726190607569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583446643187150793738379 2375169964780726190607569)
      ·
        refine ⟨1781377473585544642955677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375169964780726190607569 1781377473585544642955677)
        ·
          refine ⟨668016552594579241108379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1781377473585544642955677 668016552594579241108379)
          ·
            refine ⟨1002024828891868861662569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668016552594579241108379 1002024828891868861662569)
            ·
              refine ⟨751518621668901646246927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002024828891868861662569 751518621668901646246927)
              ·
                refine ⟨1127277932503352469370391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751518621668901646246927 1127277932503352469370391)
                ·
                  refine ⟨1690916898755028704055587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127277932503352469370391 1690916898755028704055587)
                  ·
                    refine ⟨2536375348132543056083381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690916898755028704055587 2536375348132543056083381)
                    ·
                      refine ⟨237785188887425911507817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2536375348132543056083381 237785188887425911507817)
                      ·
                        rfl

theorem cell23_463085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_463085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463085 prefixEnd_463085 := by exact prefixLift 463085
  have htrace : WordTrace (prefixWord ++ tailWord_463085) baseStart_463085 baseEnd_463085 := by
    simpa [prefixWord, tailWord_463085, baseEnd_463085] using wordTrace_append hprefix tailTrace_463085
  have hstable : (prefixWord ++ tailWord_463085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463085).length < 2 ^ (prefixWord ++ tailWord_463085).sum := by decide
  have hdescent : baseEnd_463085 < baseStart_463085 := by decide
  rcases family_descends (prefixWord ++ tailWord_463085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463115 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 3]
def baseStart_463115 : Nat := 118140960795 + 463115 * 2 ^ 59
def prefixEnd_463115 : Nat := 4983230072969 + 3 ^ 40 * 463115 * 2
def baseEnd_463115 : Nat := 237800593307060794132679

theorem tailTrace_463115 : CollatzResearch.WordTrace tailWord_463115 prefixEnd_463115 237800593307060794132679 := by
  unfold tailWord_463115
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891191717220923590134799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11260794478147282393423199 16891191717220923590134799)
  ·
    refine ⟨25336787575831385385202199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891191717220923590134799 25336787575831385385202199)
    ·
      refine ⟨38005181363747078077803299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336787575831385385202199 38005181363747078077803299)
      ·
        refine ⟨57007772045620617116704949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38005181363747078077803299 57007772045620617116704949)
        ·
          refine ⟨5344478629276932854691089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57007772045620617116704949 5344478629276932854691089)
          ·
            refine ⟨4008358971957699641018317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344478629276932854691089 4008358971957699641018317)
            ·
              refine ⟨1503134614484137365381869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4008358971957699641018317 1503134614484137365381869)
              ·
                refine ⟨563675480431551512018201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503134614484137365381869 563675480431551512018201)
                ·
                  refine ⟨422756610323663634013651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563675480431551512018201 422756610323663634013651)
                  ·
                    refine ⟨634134915485495451020477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422756610323663634013651 634134915485495451020477)
                    ·
                      refine ⟨237800593307060794132679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 634134915485495451020477 237800593307060794132679)
                      ·
                        rfl

theorem cell23_463115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 3].length) (baseStart_463115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463115 prefixEnd_463115 := by exact prefixLift 463115
  have htrace : WordTrace (prefixWord ++ tailWord_463115) baseStart_463115 baseEnd_463115 := by
    simpa [prefixWord, tailWord_463115, baseEnd_463115] using wordTrace_append hprefix tailTrace_463115
  have hstable : (prefixWord ++ tailWord_463115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463115).length < 2 ^ (prefixWord ++ tailWord_463115).sum := by decide
  have hdescent : baseEnd_463115 < baseStart_463115 := by decide
  rcases family_descends (prefixWord ++ tailWord_463115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463150 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_463150 : Nat := 118140960795 + 463150 * 2 ^ 59
def prefixEnd_463150 : Nat := 4983230072969 + 3 ^ 40 * 463150 * 2
def baseEnd_463150 : Nat := 237818565129968157195019

theorem tailTrace_463150 : CollatzResearch.WordTrace tailWord_463150 prefixEnd_463150 237818565129968157195019 := by
  unfold tailWord_463150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111558534011765570957363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11261645514729416378439269 2111558534011765570957363)
  ·
    refine ⟨3167337801017648356436045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111558534011765570957363 3167337801017648356436045)
    ·
      refine ⟨1187751675381618133663517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3167337801017648356436045 1187751675381618133663517)
      ·
        refine ⟨445406878268106800123819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1187751675381618133663517 445406878268106800123819)
        ·
          refine ⟨668110317402160200185729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445406878268106800123819 668110317402160200185729)
          ·
            refine ⟨501082738051620150139297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668110317402160200185729 501082738051620150139297)
            ·
              refine ⟨375812053538715112604473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501082738051620150139297 375812053538715112604473)
              ·
                refine ⟨281859040154036334453355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375812053538715112604473 281859040154036334453355)
                ·
                  refine ⟨422788560231054501680033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281859040154036334453355 422788560231054501680033)
                  ·
                    refine ⟨317091420173290876260025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 422788560231054501680033 317091420173290876260025)
                    ·
                      refine ⟨237818565129968157195019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317091420173290876260025 237818565129968157195019)
                      ·
                        rfl

theorem cell23_463150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_463150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463150 prefixEnd_463150 := by exact prefixLift 463150
  have htrace : WordTrace (prefixWord ++ tailWord_463150) baseStart_463150 baseEnd_463150 := by
    simpa [prefixWord, tailWord_463150, baseEnd_463150] using wordTrace_append hprefix tailTrace_463150
  have hstable : (prefixWord ++ tailWord_463150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463150).length < 2 ^ (prefixWord ++ tailWord_463150).sum := by decide
  have hdescent : baseEnd_463150 < baseStart_463150 := by decide
  rcases family_descends (prefixWord ++ tailWord_463150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463228 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_463228 : Nat := 118140960795 + 463228 * 2 ^ 59
def prefixEnd_463228 : Nat := 4983230072969 + 3 ^ 40 * 463228 * 2
def baseEnd_463228 : Nat := 237858616621018852019659

theorem tailTrace_463228 : CollatzResearch.WordTrace tailWord_463228 prefixEnd_463228 237858616621018852019659 := by
  unfold tailWord_463228
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447656582905771944499169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11263542110541029259332225 8447656582905771944499169)
  ·
    refine ⟨6335742437179328958374377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8447656582905771944499169 6335742437179328958374377)
    ·
      refine ⟨4751806827884496718780783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6335742437179328958374377 4751806827884496718780783)
      ·
        refine ⟨7127710241826745078171175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751806827884496718780783 7127710241826745078171175)
        ·
          refine ⟨10691565362740117617256763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127710241826745078171175 10691565362740117617256763)
          ·
            refine ⟨16037348044110176425885145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691565362740117617256763 16037348044110176425885145)
            ·
              refine ⟨12028011033082632319413859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16037348044110176425885145 12028011033082632319413859)
              ·
                refine ⟨18042016549623948479120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12028011033082632319413859 18042016549623948479120789)
                ·
                  refine ⟨845719525763622584958787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18042016549623948479120789 845719525763622584958787)
                  ·
                    refine ⟨1268579288645433877438181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845719525763622584958787 1268579288645433877438181)
                    ·
                      refine ⟨237858616621018852019659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1268579288645433877438181 237858616621018852019659)
                      ·
                        rfl

theorem cell23_463228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_463228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463228 prefixEnd_463228 := by exact prefixLift 463228
  have htrace : WordTrace (prefixWord ++ tailWord_463228) baseStart_463228 baseEnd_463228 := by
    simpa [prefixWord, tailWord_463228, baseEnd_463228] using wordTrace_append hprefix tailTrace_463228
  have hstable : (prefixWord ++ tailWord_463228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463228).length < 2 ^ (prefixWord ++ tailWord_463228).sum := by decide
  have hdescent : baseEnd_463228 < baseStart_463228 := by decide
  rcases family_descends (prefixWord ++ tailWord_463228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463262 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_463262 : Nat := 118140960795 + 463262 * 2 ^ 59
def prefixEnd_463262 : Nat := 4983230072969 + 3 ^ 40 * 463262 * 2
def baseEnd_463262 : Nat := 237876074963271718994503

theorem tailTrace_463262 : CollatzResearch.WordTrace tailWord_463262 prefixEnd_463262 237876074963271718994503 := by
  unfold tailWord_463262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112069155961045961967005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11264368831792245130490693 2112069155961045961967005)
  ·
    refine ⟨792025933485392235737627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2112069155961045961967005 792025933485392235737627)
    ·
      refine ⟨1188038900228088353606441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792025933485392235737627 1188038900228088353606441)
      ·
        refine ⟨891029175171066265204831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188038900228088353606441 891029175171066265204831)
        ·
          refine ⟨1336543762756599397807247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891029175171066265204831 1336543762756599397807247)
          ·
            refine ⟨2004815644134899096710871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336543762756599397807247 2004815644134899096710871)
            ·
              refine ⟨3007223466202348645066307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004815644134899096710871 3007223466202348645066307)
              ·
                refine ⟨4510835199303522967599461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007223466202348645066307 4510835199303522967599461)
                ·
                  refine ⟨845781599869410556424899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4510835199303522967599461 845781599869410556424899)
                  ·
                    refine ⟨1268672399804115834637349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845781599869410556424899 1268672399804115834637349)
                    ·
                      refine ⟨237876074963271718994503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1268672399804115834637349 237876074963271718994503)
                      ·
                        rfl

theorem cell23_463262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_463262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463262 prefixEnd_463262 := by exact prefixLift 463262
  have htrace : WordTrace (prefixWord ++ tailWord_463262) baseStart_463262 baseEnd_463262 := by
    simpa [prefixWord, tailWord_463262, baseEnd_463262] using wordTrace_append hprefix tailTrace_463262
  have hstable : (prefixWord ++ tailWord_463262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463262).length < 2 ^ (prefixWord ++ tailWord_463262).sum := by decide
  have hdescent : baseEnd_463262 < baseStart_463262 := by decide
  rcases family_descends (prefixWord ++ tailWord_463262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463268 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 8]
def baseStart_463268 : Nat := 118140960795 + 463268 * 2 ^ 59
def prefixEnd_463268 : Nat := 4983230072969 + 3 ^ 40 * 463268 * 2
def baseEnd_463268 : Nat := 26431017316355410613275

theorem tailTrace_463268 : CollatzResearch.WordTrace tailWord_463268 prefixEnd_463268 26431017316355410613275 := by
  unfold tailWord_463268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448386042833315360227229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11264514723777753813636305 8448386042833315360227229)
  ·
    refine ⟨3168144766062493260085211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8448386042833315360227229 3168144766062493260085211)
    ·
      refine ⟨4752217149093739890127817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168144766062493260085211 4752217149093739890127817)
      ·
        refine ⟨3564162861820304917595863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4752217149093739890127817 3564162861820304917595863)
        ·
          refine ⟨5346244292730457376393795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564162861820304917595863 5346244292730457376393795)
          ·
            refine ⟨8019366439095686064590693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346244292730457376393795 8019366439095686064590693)
            ·
              refine ⟨1503631207330441137110755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8019366439095686064590693 1503631207330441137110755)
              ·
                refine ⟨2255446810995661705666133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503631207330441137110755 2255446810995661705666133)
                ·
                  refine ⟨26431017316355410613275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2255446810995661705666133 26431017316355410613275)
                  ·
                    rfl

theorem cell23_463268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_463268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463268 prefixEnd_463268 := by exact prefixLift 463268
  have htrace : WordTrace (prefixWord ++ tailWord_463268) baseStart_463268 baseEnd_463268 := by
    simpa [prefixWord, tailWord_463268, baseEnd_463268] using wordTrace_append hprefix tailTrace_463268
  have hstable : (prefixWord ++ tailWord_463268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463268).length < 2 ^ (prefixWord ++ tailWord_463268).sum := by decide
  have hdescent : baseEnd_463268 < baseStart_463268 := by decide
  rcases family_descends (prefixWord ++ tailWord_463268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463305 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 5, 2]
def baseStart_463305 : Nat := 118140960795 + 463305 * 2 ^ 59
def prefixEnd_463305 : Nat := 4983230072969 + 3 ^ 40 * 463305 * 2
def baseEnd_463305 : Nat := 237898154631415050756805

theorem tailTrace_463305 : CollatzResearch.WordTrace tailWord_463305 prefixEnd_463305 237898154631415050756805 := by
  unfold tailWord_463305
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898121586532586039551369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11265414391021724026367579 16898121586532586039551369)
  ·
    refine ⟨12673591189899439529663527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16898121586532586039551369 12673591189899439529663527)
    ·
      refine ⟨19010386784849159294495291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673591189899439529663527 19010386784849159294495291)
      ·
        refine ⟨28515580177273738941742937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010386784849159294495291 28515580177273738941742937)
        ·
          refine ⟨21386685132955304206307203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28515580177273738941742937 21386685132955304206307203)
          ·
            refine ⟨32080027699432956309460805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21386685132955304206307203 32080027699432956309460805)
            ·
              refine ⟨6015005193643679308023901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32080027699432956309460805 6015005193643679308023901)
              ·
                refine ⟨2255626947616379740508963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6015005193643679308023901 2255626947616379740508963)
                ·
                  refine ⟨3383440421424569610763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255626947616379740508963 3383440421424569610763445)
                  ·
                    refine ⟨317197539508553401009073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3383440421424569610763445 317197539508553401009073)
                    ·
                      refine ⟨237898154631415050756805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317197539508553401009073 237898154631415050756805)
                      ·
                        rfl

theorem cell23_463305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5, 2].length) (baseStart_463305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463305 prefixEnd_463305 := by exact prefixLift 463305
  have htrace : WordTrace (prefixWord ++ tailWord_463305) baseStart_463305 baseEnd_463305 := by
    simpa [prefixWord, tailWord_463305, baseEnd_463305] using wordTrace_append hprefix tailTrace_463305
  have hstable : (prefixWord ++ tailWord_463305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463305).length < 2 ^ (prefixWord ++ tailWord_463305).sum := by decide
  have hdescent : baseEnd_463305 < baseStart_463305 := by decide
  rcases family_descends (prefixWord ++ tailWord_463305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463322 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_463322 : Nat := 118140960795 + 463322 * 2 ^ 59
def prefixEnd_463322 : Nat := 4983230072969 + 3 ^ 40 * 463322 * 2
def baseEnd_463322 : Nat := 237906883802541484244227

theorem tailTrace_463322 : CollatzResearch.WordTrace tailWord_463322 prefixEnd_463322 237906883802541484244227 := by
  unfold tailWord_463322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224685406867749485730055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11265827751647331961946813 4224685406867749485730055)
  ·
    refine ⟨6337028110301624228595083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4224685406867749485730055 6337028110301624228595083)
    ·
      refine ⟨9505542165452436342892625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337028110301624228595083 9505542165452436342892625)
      ·
        refine ⟨7129156624089327257169469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9505542165452436342892625 7129156624089327257169469)
        ·
          refine ⟨2673433734033497721438551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7129156624089327257169469 2673433734033497721438551)
          ·
            refine ⟨4010150601050246582157827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673433734033497721438551 4010150601050246582157827)
            ·
              refine ⟨6015225901575369873236741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010150601050246582157827 6015225901575369873236741)
              ·
                refine ⟨1127854856545381851231889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6015225901575369873236741 1127854856545381851231889)
                ·
                  refine ⟨845891142409036388423917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1127854856545381851231889 845891142409036388423917)
                  ·
                    refine ⟨317209178403388645658969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 845891142409036388423917 317209178403388645658969)
                    ·
                      refine ⟨237906883802541484244227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317209178403388645658969 237906883802541484244227)
                      ·
                        rfl

theorem cell23_463322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_463322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463322 prefixEnd_463322 := by exact prefixLift 463322
  have htrace : WordTrace (prefixWord ++ tailWord_463322) baseStart_463322 baseEnd_463322 := by
    simpa [prefixWord, tailWord_463322, baseEnd_463322] using wordTrace_append hprefix tailTrace_463322
  have hstable : (prefixWord ++ tailWord_463322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463322).length < 2 ^ (prefixWord ++ tailWord_463322).sum := by decide
  have hdescent : baseEnd_463322 < baseStart_463322 := by decide
  rcases family_descends (prefixWord ++ tailWord_463322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463328 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_463328 : Nat := 118140960795 + 463328 * 2 ^ 59
def prefixEnd_463328 : Nat := 4983230072969 + 3 ^ 40 * 463328 * 2
def baseEnd_463328 : Nat := 79303321562156153589733

theorem tailTrace_463328 : CollatzResearch.WordTrace tailWord_463328 prefixEnd_463328 79303321562156153589733 := by
  unfold tailWord_463328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449480232724630483819319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11265973643632840645092425 8449480232724630483819319)
  ·
    refine ⟨12674220349086945725728979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449480232724630483819319 12674220349086945725728979)
    ·
      refine ⟨19011330523630418588593469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12674220349086945725728979 19011330523630418588593469)
      ·
        refine ⟨7129248946361406970722551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19011330523630418588593469 7129248946361406970722551)
        ·
          refine ⟨10693873419542110456083827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129248946361406970722551 10693873419542110456083827)
          ·
            refine ⟨16040810129313165684125741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10693873419542110456083827 16040810129313165684125741)
            ·
              refine ⟨6015303798492437131547153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16040810129313165684125741 6015303798492437131547153)
              ·
                refine ⟨4511477848869327848660365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015303798492437131547153 4511477848869327848660365)
                ·
                  refine ⟨1691804193325997943247637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4511477848869327848660365 1691804193325997943247637)
                  ·
                    refine ⟨79303321562156153589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1691804193325997943247637 79303321562156153589733)
                    ·
                      rfl

theorem cell23_463328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_463328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463328 prefixEnd_463328 := by exact prefixLift 463328
  have htrace : WordTrace (prefixWord ++ tailWord_463328) baseStart_463328 baseEnd_463328 := by
    simpa [prefixWord, tailWord_463328, baseEnd_463328] using wordTrace_append hprefix tailTrace_463328
  have hstable : (prefixWord ++ tailWord_463328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463328).length < 2 ^ (prefixWord ++ tailWord_463328).sum := by decide
  have hdescent : baseEnd_463328 < baseStart_463328 := by decide
  rcases family_descends (prefixWord ++ tailWord_463328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463329 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_463329 : Nat := 118140960795 + 463329 * 2 ^ 59
def prefixEnd_463329 : Nat := 4983230072969 + 3 ^ 40 * 463329 * 2
def baseEnd_463329 : Nat := 237910478167122956856695

theorem tailTrace_463329 : CollatzResearch.WordTrace tailWord_463329 prefixEnd_463329 237910478167122956856695 := by
  unfold tailWord_463329
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898996938445638138425041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11265997958963758758950027 16898996938445638138425041)
  ·
    refine ⟨12674247703834228603818781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16898996938445638138425041 12674247703834228603818781)
    ·
      refine ⟨4752842888937835726432043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12674247703834228603818781 4752842888937835726432043)
      ·
        refine ⟨7129264333406753589648065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752842888937835726432043 7129264333406753589648065)
        ·
          refine ⟨5346948250055065192236049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129264333406753589648065 5346948250055065192236049)
          ·
            refine ⟨4010211187541298894177037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5346948250055065192236049 4010211187541298894177037)
            ·
              refine ⟨1503829195327987085316389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4010211187541298894177037 1503829195327987085316389)
              ·
                refine ⟨281967974123997578496823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1503829195327987085316389 281967974123997578496823)
                ·
                  refine ⟨422951961185996367745235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281967974123997578496823 422951961185996367745235)
                  ·
                    refine ⟨634427941778994551617853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422951961185996367745235 634427941778994551617853)
                    ·
                      refine ⟨237910478167122956856695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 634427941778994551617853 237910478167122956856695)
                      ·
                        rfl

theorem cell23_463329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_463329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463329 prefixEnd_463329 := by exact prefixLift 463329
  have htrace : WordTrace (prefixWord ++ tailWord_463329) baseStart_463329 baseEnd_463329 := by
    simpa [prefixWord, tailWord_463329, baseEnd_463329] using wordTrace_append hprefix tailTrace_463329
  have hstable : (prefixWord ++ tailWord_463329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463329).length < 2 ^ (prefixWord ++ tailWord_463329).sum := by decide
  have hdescent : baseEnd_463329 < baseStart_463329 := by decide
  rcases family_descends (prefixWord ++ tailWord_463329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463335 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_463335 : Nat := 118140960795 + 463335 * 2 ^ 59
def prefixEnd_463335 : Nat := 4983230072969 + 3 ^ 40 * 463335 * 2
def baseEnd_463335 : Nat := 237913559051049933381667

theorem tailTrace_463335 : CollatzResearch.WordTrace tailWord_463335 prefixEnd_463335 237913559051049933381667 := by
  unfold tailWord_463335
  simp only [CollatzResearch.WordTrace]
  refine ⟨16899215776423901163143459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11266143850949267442095639 16899215776423901163143459)
  ·
    refine ⟨25348823664635851744715189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16899215776423901163143459 25348823664635851744715189)
    ·
      refine ⟨2376452218559611101067049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25348823664635851744715189 2376452218559611101067049)
      ·
        refine ⟨1782339163919708325800287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376452218559611101067049 1782339163919708325800287)
        ·
          refine ⟨2673508745879562488700431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782339163919708325800287 2673508745879562488700431)
          ·
            refine ⟨4010263118819343733050647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673508745879562488700431 4010263118819343733050647)
            ·
              refine ⟨6015394678229015599575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010263118819343733050647 6015394678229015599575971)
              ·
                refine ⟨9023092017343523399363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015394678229015599575971 9023092017343523399363957)
                ·
                  refine ⟨845914876625955318690371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9023092017343523399363957 845914876625955318690371)
                  ·
                    refine ⟨1268872314938932978035557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845914876625955318690371 1268872314938932978035557)
                    ·
                      refine ⟨237913559051049933381667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1268872314938932978035557 237913559051049933381667)
                      ·
                        rfl

theorem cell23_463335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_463335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463335 prefixEnd_463335 := by exact prefixLift 463335
  have htrace : WordTrace (prefixWord ++ tailWord_463335) baseStart_463335 baseEnd_463335 := by
    simpa [prefixWord, tailWord_463335, baseEnd_463335] using wordTrace_append hprefix tailTrace_463335
  have hstable : (prefixWord ++ tailWord_463335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463335).length < 2 ^ (prefixWord ++ tailWord_463335).sum := by decide
  have hdescent : baseEnd_463335 < baseStart_463335 := by decide
  rcases family_descends (prefixWord ++ tailWord_463335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463345 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_463345 : Nat := 118140960795 + 463345 * 2 ^ 59
def prefixEnd_463345 : Nat := 4983230072969 + 3 ^ 40 * 463345 * 2
def baseEnd_463345 : Nat := 79306231285864964752207

theorem tailTrace_463345 : CollatzResearch.WordTrace tailWord_463345 prefixEnd_463345 79306231285864964752207 := by
  unfold tailWord_463345
  simp only [CollatzResearch.WordTrace]
  refine ⟨16899580506387672871007489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11266387004258448580671659 16899580506387672871007489)
  ·
    refine ⟨12674685379790754653255617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16899580506387672871007489 12674685379790754653255617)
    ·
      refine ⟨9506014034843065989941713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12674685379790754653255617 9506014034843065989941713)
      ·
        refine ⟨7129510526132299492456285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9506014034843065989941713 7129510526132299492456285)
        ·
          refine ⟨2673566447299612309671107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7129510526132299492456285 2673566447299612309671107)
          ·
            refine ⟨4010349670949418464506661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673566447299612309671107 4010349670949418464506661)
            ·
              refine ⟨751940563303015962094999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4010349670949418464506661 751940563303015962094999)
              ·
                refine ⟨1127910844954523943142499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751940563303015962094999 1127910844954523943142499)
                ·
                  refine ⟨1691866267431785914713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127910844954523943142499 1691866267431785914713749)
                  ·
                    refine ⟨79306231285864964752207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1691866267431785914713749 79306231285864964752207)
                    ·
                      rfl

theorem cell23_463345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_463345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463345 prefixEnd_463345 := by exact prefixLift 463345
  have htrace : WordTrace (prefixWord ++ tailWord_463345) baseStart_463345 baseEnd_463345 := by
    simpa [prefixWord, tailWord_463345, baseEnd_463345] using wordTrace_append hprefix tailTrace_463345
  have hstable : (prefixWord ++ tailWord_463345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463345).length < 2 ^ (prefixWord ++ tailWord_463345).sum := by decide
  have hdescent : baseEnd_463345 < baseStart_463345 := by decide
  rcases family_descends (prefixWord ++ tailWord_463345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463365 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_463365 : Nat := 118140960795 + 463365 * 2 ^ 59
def prefixEnd_463365 : Nat := 4983230072969 + 3 ^ 40 * 463365 * 2
def baseEnd_463365 : Nat := 237928963470684816006529

theorem tailTrace_463365 : CollatzResearch.WordTrace tailWord_463365 prefixEnd_463365 237928963470684816006529 := by
  unfold tailWord_463365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16900309966315216286735549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11266873310876810857823699 16900309966315216286735549)
  ·
    refine ⟨6337616237368206107525831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16900309966315216286735549 6337616237368206107525831)
    ·
      refine ⟨9506424356052309161288747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337616237368206107525831 9506424356052309161288747)
      ·
        refine ⟨14259636534078463741933121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9506424356052309161288747 14259636534078463741933121)
        ·
          refine ⟨10694727400558847806449841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14259636534078463741933121 10694727400558847806449841)
          ·
            refine ⟨8021045550419135854837381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10694727400558847806449841 8021045550419135854837381)
            ·
              refine ⟨1503946040703587972782009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8021045550419135854837381 1503946040703587972782009)
              ·
                refine ⟨1127959530527690979586507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503946040703587972782009 1127959530527690979586507)
                ·
                  refine ⟨1691939295791536469379761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127959530527690979586507 1691939295791536469379761)
                  ·
                    refine ⟨1268954471843652352034821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1691939295791536469379761 1268954471843652352034821)
                    ·
                      refine ⟨237928963470684816006529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1268954471843652352034821 237928963470684816006529)
                      ·
                        rfl

theorem cell23_463365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_463365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463365 prefixEnd_463365 := by exact prefixLift 463365
  have htrace : WordTrace (prefixWord ++ tailWord_463365) baseStart_463365 baseEnd_463365 := by
    simpa [prefixWord, tailWord_463365, baseEnd_463365] using wordTrace_append hprefix tailTrace_463365
  have hstable : (prefixWord ++ tailWord_463365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463365).length < 2 ^ (prefixWord ++ tailWord_463365).sum := by decide
  have hdescent : baseEnd_463365 < baseStart_463365 := by decide
  rcases family_descends (prefixWord ++ tailWord_463365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463386 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_463386 : Nat := 118140960795 + 463386 * 2 ^ 59
def prefixEnd_463386 : Nat := 4983230072969 + 3 ^ 40 * 463386 * 2
def baseEnd_463386 : Nat := 237939746564429233843933

theorem tailTrace_463386 : CollatzResearch.WordTrace tailWord_463386 prefixEnd_463386 237939746564429233843933 := by
  unfold tailWord_463386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225268974809784218312503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11267383932826091248833341 4225268974809784218312503)
  ·
    refine ⟨6337903462214676327468755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225268974809784218312503 6337903462214676327468755)
    ·
      refine ⟨9506855193322014491203133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337903462214676327468755 9506855193322014491203133)
      ·
        refine ⟨3565070697495755434201175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9506855193322014491203133 3565070697495755434201175)
        ·
          refine ⟨5347606046243633151301763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565070697495755434201175 5347606046243633151301763)
          ·
            refine ⟨8021409069365449726952645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347606046243633151301763 8021409069365449726952645)
            ·
              refine ⟨1504014200506021823803621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8021409069365449726952645 1504014200506021823803621)
              ·
                refine ⟨282002662594879091963179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1504014200506021823803621 282002662594879091963179)
                ·
                  refine ⟨423003993892318637944769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282002662594879091963179 423003993892318637944769)
                  ·
                    refine ⟨317252995419238978458577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423003993892318637944769 317252995419238978458577)
                    ·
                      refine ⟨237939746564429233843933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317252995419238978458577 237939746564429233843933)
                      ·
                        rfl

theorem cell23_463386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_463386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463386 prefixEnd_463386 := by exact prefixLift 463386
  have htrace : WordTrace (prefixWord ++ tailWord_463386) baseStart_463386 baseEnd_463386 := by
    simpa [prefixWord, tailWord_463386, baseEnd_463386] using wordTrace_append hprefix tailTrace_463386
  have hstable : (prefixWord ++ tailWord_463386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463386).length < 2 ^ (prefixWord ++ tailWord_463386).sum := by decide
  have hdescent : baseEnd_463386 < baseStart_463386 := by decide
  rcases family_descends (prefixWord ++ tailWord_463386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463396 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_463396 : Nat := 118140960795 + 463396 * 2 ^ 59
def prefixEnd_463396 : Nat := 4983230072969 + 3 ^ 40 * 463396 * 2
def baseEnd_463396 : Nat := 79314960456991398239629

theorem tailTrace_463396 : CollatzResearch.WordTrace tailWord_463396 prefixEnd_463396 79314960456991398239629 := by
  unfold tailWord_463396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8450720314601454290557021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11267627086135272387409361 8450720314601454290557021)
  ·
    refine ⟨3169020117975545358958883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8450720314601454290557021 3169020117975545358958883)
    ·
      refine ⟨4753530176963318038438325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3169020117975545358958883 4753530176963318038438325)
      ·
        refine ⟨445643454090311066103593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4753530176963318038438325 445643454090311066103593)
        ·
          refine ⟨334232590567733299577695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445643454090311066103593 334232590567733299577695)
          ·
            refine ⟨501348885851599949366543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334232590567733299577695 501348885851599949366543)
            ·
              refine ⟨752023328777399924049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501348885851599949366543 752023328777399924049815)
              ·
                refine ⟨1128034993166099886074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752023328777399924049815 1128034993166099886074723)
                ·
                  refine ⟨1692052489749149829112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128034993166099886074723 1692052489749149829112085)
                  ·
                    refine ⟨79314960456991398239629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1692052489749149829112085 79314960456991398239629)
                    ·
                      rfl

theorem cell23_463396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_463396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463396 prefixEnd_463396 := by exact prefixLift 463396
  have htrace : WordTrace (prefixWord ++ tailWord_463396) baseStart_463396 baseEnd_463396 := by
    simpa [prefixWord, tailWord_463396, baseEnd_463396] using wordTrace_append hprefix tailTrace_463396
  have hstable : (prefixWord ++ tailWord_463396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463396).length < 2 ^ (prefixWord ++ tailWord_463396).sum := by decide
  have hdescent : baseEnd_463396 < baseStart_463396 := by decide
  rcases family_descends (prefixWord ++ tailWord_463396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463399 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_463399 : Nat := 118140960795 + 463399 * 2 ^ 59
def prefixEnd_463399 : Nat := 4983230072969 + 3 ^ 40 * 463399 * 2
def baseEnd_463399 : Nat := 237946421812937682981373

theorem tailTrace_463399 : CollatzResearch.WordTrace tailWord_463399 prefixEnd_463399 237946421812937682981373 := by
  unfold tailWord_463399
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901550048192040093473251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11267700032128026728982167 16901550048192040093473251)
  ·
    refine ⟨25352325072288060140209877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16901550048192040093473251 25352325072288060140209877)
    ·
      refine ⟨594195118881751409536169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25352325072288060140209877 594195118881751409536169)
      ·
        refine ⟨445646339161313557152127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594195118881751409536169 445646339161313557152127)
        ·
          refine ⟨668469508741970335728191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445646339161313557152127 668469508741970335728191)
          ·
            refine ⟨1002704263112955503592287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668469508741970335728191 1002704263112955503592287)
            ·
              refine ⟨1504056394669433255388431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002704263112955503592287 1504056394669433255388431)
              ·
                refine ⟨2256084592004149883082647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504056394669433255388431 2256084592004149883082647)
                ·
                  refine ⟨3384126888006224824623971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256084592004149883082647 3384126888006224824623971)
                  ·
                    refine ⟨5076190332009337236935957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384126888006224824623971 5076190332009337236935957)
                    ·
                      refine ⟨237946421812937682981373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5076190332009337236935957 237946421812937682981373)
                      ·
                        rfl

theorem cell23_463399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_463399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463399 prefixEnd_463399 := by exact prefixLift 463399
  have htrace : WordTrace (prefixWord ++ tailWord_463399) baseStart_463399 baseEnd_463399 := by
    simpa [prefixWord, tailWord_463399, baseEnd_463399] using wordTrace_append hprefix tailTrace_463399
  have hstable : (prefixWord ++ tailWord_463399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463399).length < 2 ^ (prefixWord ++ tailWord_463399).sum := by decide
  have hdescent : baseEnd_463399 < baseStart_463399 := by decide
  rcases family_descends (prefixWord ++ tailWord_463399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463406 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_463406 : Nat := 118140960795 + 463406 * 2 ^ 59
def prefixEnd_463406 : Nat := 4983230072969 + 3 ^ 40 * 463406 * 2
def baseEnd_463406 : Nat := 237950016177519155593841

theorem tailTrace_463406 : CollatzResearch.WordTrace tailWord_463406 prefixEnd_463406 237950016177519155593841 := by
  unfold tailWord_463406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112725669895835036122259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11267870239444453525985381 2112725669895835036122259)
  ·
    refine ⟨3169088504843752554183389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112725669895835036122259 3169088504843752554183389)
    ·
      refine ⟨1188408189316407207818771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3169088504843752554183389 1188408189316407207818771)
      ·
        refine ⟨1782612283974610811728157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188408189316407207818771 1782612283974610811728157)
        ·
          refine ⟨668479606490479054398059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782612283974610811728157 668479606490479054398059)
          ·
            refine ⟨1002719409735718581597089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668479606490479054398059 1002719409735718581597089)
            ·
              refine ⟨752039557301788936197817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002719409735718581597089 752039557301788936197817)
              ·
                refine ⟨564029667976341702148363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752039557301788936197817 564029667976341702148363)
                ·
                  refine ⟨846044501964512553222545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564029667976341702148363 846044501964512553222545)
                  ·
                    refine ⟨634533376473384414916909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846044501964512553222545 634533376473384414916909)
                    ·
                      refine ⟨237950016177519155593841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 634533376473384414916909 237950016177519155593841)
                      ·
                        rfl

theorem cell23_463406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_463406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463406 prefixEnd_463406 := by exact prefixLift 463406
  have htrace : WordTrace (prefixWord ++ tailWord_463406) baseStart_463406 baseEnd_463406 := by
    simpa [prefixWord, tailWord_463406, baseEnd_463406] using wordTrace_append hprefix tailTrace_463406
  have hstable : (prefixWord ++ tailWord_463406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463406).length < 2 ^ (prefixWord ++ tailWord_463406).sum := by decide
  have hdescent : baseEnd_463406 < baseStart_463406 := by decide
  rcases family_descends (prefixWord ++ tailWord_463406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463429 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_463429 : Nat := 118140960795 + 463429 * 2 ^ 59
def prefixEnd_463429 : Nat := 4983230072969 + 3 ^ 40 * 463429 * 2
def baseEnd_463429 : Nat := 237961826232572565606235

theorem tailTrace_463429 : CollatzResearch.WordTrace tailWord_463429 prefixEnd_463429 237961826232572565606235 := by
  unfold tailWord_463429
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902644238083355217065341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11268429492055570144710227 16902644238083355217065341)
  ·
    refine ⟨6338491589281258206399503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16902644238083355217065341 6338491589281258206399503)
    ·
      refine ⟨9507737383921887309599255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6338491589281258206399503 9507737383921887309599255)
      ·
        refine ⟨14261606075882830964398883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9507737383921887309599255 14261606075882830964398883)
        ·
          refine ⟨21392409113824246446598325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261606075882830964398883 21392409113824246446598325)
          ·
            refine ⟨2005538354421023104368593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21392409113824246446598325 2005538354421023104368593)
            ·
              refine ⟨1504153765815767328276445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005538354421023104368593 1504153765815767328276445)
              ·
                refine ⟨564057662180912748103667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504153765815767328276445 564057662180912748103667)
                ·
                  refine ⟨846086493271369122155501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564057662180912748103667 846086493271369122155501)
                  ·
                    refine ⟨317282434976763420808313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 846086493271369122155501 317282434976763420808313)
                    ·
                      refine ⟨237961826232572565606235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317282434976763420808313 237961826232572565606235)
                      ·
                        rfl

theorem cell23_463429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_463429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463429 prefixEnd_463429 := by exact prefixLift 463429
  have htrace : WordTrace (prefixWord ++ tailWord_463429) baseStart_463429 baseEnd_463429 := by
    simpa [prefixWord, tailWord_463429, baseEnd_463429] using wordTrace_append hprefix tailTrace_463429
  have hstable : (prefixWord ++ tailWord_463429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463429).length < 2 ^ (prefixWord ++ tailWord_463429).sum := by decide
  have hdescent : baseEnd_463429 < baseStart_463429 := by decide
  rcases family_descends (prefixWord ++ tailWord_463429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463455 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_463455 : Nat := 118140960795 + 463455 * 2 ^ 59
def prefixEnd_463455 : Nat := 4983230072969 + 3 ^ 40 * 463455 * 2
def baseEnd_463455 : Nat := 237975176729589463881115

theorem tailTrace_463455 : CollatzResearch.WordTrace tailWord_463455 prefixEnd_463455 237975176729589463881115 := by
  unfold tailWord_463455
  simp only [CollatzResearch.WordTrace]
  refine ⟨16903592535989161657511819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11269061690659441105007879 16903592535989161657511819)
  ·
    refine ⟨25355388803983742486267729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16903592535989161657511819 25355388803983742486267729)
    ·
      refine ⟨19016541602987806864700797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25355388803983742486267729 19016541602987806864700797)
      ·
        refine ⟨7131203101120427574262799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19016541602987806864700797 7131203101120427574262799)
        ·
          refine ⟨10696804651680641361394199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7131203101120427574262799 10696804651680641361394199)
          ·
            refine ⟨16045206977520962042091299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696804651680641361394199 16045206977520962042091299)
            ·
              refine ⟨24067810466281443063136949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045206977520962042091299 24067810466281443063136949)
              ·
                refine ⟨2256357231213885287169089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24067810466281443063136949 2256357231213885287169089)
                ·
                  refine ⟨1692267923410413965376817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256357231213885287169089 1692267923410413965376817)
                  ·
                    refine ⟨1269200942557810474032613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692267923410413965376817 1269200942557810474032613)
                    ·
                      refine ⟨237975176729589463881115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1269200942557810474032613 237975176729589463881115)
                      ·
                        rfl

theorem cell23_463455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_463455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463455 prefixEnd_463455 := by exact prefixLift 463455
  have htrace : WordTrace (prefixWord ++ tailWord_463455) baseStart_463455 baseEnd_463455 := by
    simpa [prefixWord, tailWord_463455, baseEnd_463455] using wordTrace_append hprefix tailTrace_463455
  have hstable : (prefixWord ++ tailWord_463455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463455).length < 2 ^ (prefixWord ++ tailWord_463455).sum := by decide
  have hdescent : baseEnd_463455 < baseStart_463455 := by decide
  rcases family_descends (prefixWord ++ tailWord_463455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463475 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3]
def baseStart_463475 : Nat := 118140960795 + 463475 * 2 ^ 59
def prefixEnd_463475 : Nat := 4983230072969 + 3 ^ 40 * 463475 * 2
def baseEnd_463475 : Nat := 237985446342679385631023

theorem tailTrace_463475 : CollatzResearch.WordTrace tailWord_463475 prefixEnd_463475 237985446342679385631023 := by
  unfold tailWord_463475
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904321995916705073239879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11269547997277803382159919 16904321995916705073239879)
  ·
    refine ⟨25356482993875057609859819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16904321995916705073239879 25356482993875057609859819)
    ·
      refine ⟨38034724490812586414789729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25356482993875057609859819 38034724490812586414789729)
      ·
        refine ⟨28526043368109439811092297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38034724490812586414789729 28526043368109439811092297)
        ·
          refine ⟨21394532526082079858319223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28526043368109439811092297 21394532526082079858319223)
          ·
            refine ⟨32091798789123119787478835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21394532526082079858319223 32091798789123119787478835)
            ·
              refine ⟨48137698183684679681218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32091798789123119787478835 48137698183684679681218253)
              ·
                refine ⟨18051636818881754880456845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48137698183684679681218253 18051636818881754880456845)
                ·
                  refine ⟨6769363807080658080171317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18051636818881754880456845 6769363807080658080171317)
                  ·
                    refine ⟨634627856913811695016061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6769363807080658080171317 634627856913811695016061)
                    ·
                      refine ⟨237985446342679385631023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 634627856913811695016061 237985446342679385631023)
                      ·
                        rfl

theorem cell23_463475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 3].length) (baseStart_463475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463475 prefixEnd_463475 := by exact prefixLift 463475
  have htrace : WordTrace (prefixWord ++ tailWord_463475) baseStart_463475 baseEnd_463475 := by
    simpa [prefixWord, tailWord_463475, baseEnd_463475] using wordTrace_append hprefix tailTrace_463475
  have hstable : (prefixWord ++ tailWord_463475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463475).length < 2 ^ (prefixWord ++ tailWord_463475).sum := by decide
  have hdescent : baseEnd_463475 < baseStart_463475 := by decide
  rcases family_descends (prefixWord ++ tailWord_463475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463549 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_463549 : Nat := 118140960795 + 463549 * 2 ^ 59
def prefixEnd_463549 : Nat := 4983230072969 + 3 ^ 40 * 463549 * 2
def baseEnd_463549 : Nat := 238023443911112096105683

theorem tailTrace_463549 : CollatzResearch.WordTrace tailWord_463549 prefixEnd_463549 238023443911112096105683 := by
  unfold tailWord_463549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907020997648615711433701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11271347331765743807622467 16907020997648615711433701)
  ·
    refine ⟨3170066437059115445893819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16907020997648615711433701 3170066437059115445893819)
    ·
      refine ⟨4755099655588673168840729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170066437059115445893819 4755099655588673168840729)
      ·
        refine ⟨3566324741691504876630547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4755099655588673168840729 3566324741691504876630547)
        ·
          refine ⟨5349487112537257314945821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566324741691504876630547 5349487112537257314945821)
          ·
            refine ⟨2006057667201471493104683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5349487112537257314945821 2006057667201471493104683)
            ·
              refine ⟨3009086500802207239657025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006057667201471493104683 3009086500802207239657025)
              ·
                refine ⟨2256814875601655429742769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009086500802207239657025 2256814875601655429742769)
                ·
                  refine ⟨1692611156701241572307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256814875601655429742769 1692611156701241572307077)
                  ·
                    refine ⟨317364591881482794807577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692611156701241572307077 317364591881482794807577)
                    ·
                      refine ⟨238023443911112096105683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317364591881482794807577 238023443911112096105683)
                      ·
                        rfl

theorem cell23_463549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_463549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463549 prefixEnd_463549 := by exact prefixLift 463549
  have htrace : WordTrace (prefixWord ++ tailWord_463549) baseStart_463549 baseEnd_463549 := by
    simpa [prefixWord, tailWord_463549, baseEnd_463549] using wordTrace_append hprefix tailTrace_463549
  have hstable : (prefixWord ++ tailWord_463549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463549).length < 2 ^ (prefixWord ++ tailWord_463549).sum := by decide
  have hdescent : baseEnd_463549 < baseStart_463549 := by decide
  rcases family_descends (prefixWord ++ tailWord_463549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463666 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_463666 : Nat := 118140960795 + 463666 * 2 ^ 59
def prefixEnd_463666 : Nat := 4983230072969 + 3 ^ 40 * 463666 * 2
def baseEnd_463666 : Nat := 79361173715896046114215

theorem tailTrace_463666 : CollatzResearch.WordTrace tailWord_463666 prefixEnd_463666 79361173715896046114215 := by
  unfold tailWord_463666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227822084556186173360713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11274192225483163128961901 4227822084556186173360713)
  ·
    refine ⟨3170866563417139630020535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4227822084556186173360713 3170866563417139630020535)
    ·
      refine ⟨4756299845125709445030803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170866563417139630020535 4756299845125709445030803)
      ·
        refine ⟨7134449767688564167546205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756299845125709445030803 7134449767688564167546205)
        ·
          refine ⟨2675418662883211562829827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7134449767688564167546205 2675418662883211562829827)
          ·
            refine ⟨4013127994324817344244741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675418662883211562829827 4013127994324817344244741)
            ·
              refine ⟨752461498935903252045889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4013127994324817344244741 752461498935903252045889)
              ·
                refine ⟨564346124201927439034417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752461498935903252045889 564346124201927439034417)
                ·
                  refine ⟨423259593151445579275813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564346124201927439034417 423259593151445579275813)
                  ·
                    refine ⟨79361173715896046114215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423259593151445579275813 79361173715896046114215)
                    ·
                      rfl

theorem cell23_463666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_463666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463666 prefixEnd_463666 := by exact prefixLift 463666
  have htrace : WordTrace (prefixWord ++ tailWord_463666) baseStart_463666 baseEnd_463666 := by
    simpa [prefixWord, tailWord_463666, baseEnd_463666] using wordTrace_append hprefix tailTrace_463666
  have hstable : (prefixWord ++ tailWord_463666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463666).length < 2 ^ (prefixWord ++ tailWord_463666).sum := by decide
  have hdescent : baseEnd_463666 < baseStart_463666 := by decide
  rcases family_descends (prefixWord ++ tailWord_463666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463679 : List Nat := [1, 1, 2, 2, 5, 3, 1, 8]
def baseStart_463679 : Nat := 118140960795 + 463679 * 2 ^ 59
def prefixEnd_463679 : Nat := 4983230072969 + 3 ^ 40 * 463679 * 2
def baseEnd_463679 : Nat := 8818155422081355091855

theorem tailTrace_463679 : CollatzResearch.WordTrace tailWord_463679 prefixEnd_463679 8818155422081355091855 := by
  unfold tailWord_463679
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911762487177647913666091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274508324785098609110727 16911762487177647913666091)
  ·
    refine ⟨25367643730766471870499137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16911762487177647913666091 25367643730766471870499137)
    ·
      refine ⟨19025732798074853902874353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25367643730766471870499137 19025732798074853902874353)
      ·
        refine ⟨14269299598556140427155765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19025732798074853902874353 14269299598556140427155765)
        ·
          refine ⟨1337746837364638165045853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14269299598556140427155765 1337746837364638165045853)
          ·
            refine ⟨501655064011739311892195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1337746837364638165045853 501655064011739311892195)
            ·
              refine ⟨752482596017608967838293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501655064011739311892195 752482596017608967838293)
              ·
                refine ⟨8818155422081355091855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 752482596017608967838293 8818155422081355091855)
                ·
                  rfl

theorem cell23_463679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 8].length) (baseStart_463679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463679 prefixEnd_463679 := by exact prefixLift 463679
  have htrace : WordTrace (prefixWord ++ tailWord_463679) baseStart_463679 baseEnd_463679 := by
    simpa [prefixWord, tailWord_463679, baseEnd_463679] using wordTrace_append hprefix tailTrace_463679
  have hstable : (prefixWord ++ tailWord_463679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463679).length < 2 ^ (prefixWord ++ tailWord_463679).sum := by decide
  have hdescent : baseEnd_463679 < baseStart_463679 := by decide
  rcases family_descends (prefixWord ++ tailWord_463679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463689 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_463689 : Nat := 118140960795 + 463689 * 2 ^ 59
def prefixEnd_463689 : Nat := 4983230072969 + 3 ^ 40 * 463689 * 2
def baseEnd_463689 : Nat := 238095331202741548355039

theorem tailTrace_463689 : CollatzResearch.WordTrace tailWord_463689 prefixEnd_463689 238095331202741548355039 := by
  unfold tailWord_463689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912127217141419621530121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274751478094279747686747 16912127217141419621530121)
  ·
    refine ⟨12684095412856064716147591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16912127217141419621530121 12684095412856064716147591)
    ·
      refine ⟨19026143119284097074221387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12684095412856064716147591 19026143119284097074221387)
      ·
        refine ⟨28539214678926145611332081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19026143119284097074221387 28539214678926145611332081)
        ·
          refine ⟨21404411009194609208499061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28539214678926145611332081 21404411009194609208499061)
          ·
            refine ⟨2006663532111994613296787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21404411009194609208499061 2006663532111994613296787)
            ·
              refine ⟨3009995298167991919945181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006663532111994613296787 3009995298167991919945181)
              ·
                refine ⟨1128748236812996969979443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009995298167991919945181 1128748236812996969979443)
                ·
                  refine ⟨1693122355219495454969165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128748236812996969979443 1693122355219495454969165)
                  ·
                    refine ⟨634920883207310795613437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693122355219495454969165 634920883207310795613437)
                    ·
                      refine ⟨238095331202741548355039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 634920883207310795613437 238095331202741548355039)
                      ·
                        rfl

theorem cell23_463689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_463689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463689 prefixEnd_463689 := by exact prefixLift 463689
  have htrace : WordTrace (prefixWord ++ tailWord_463689) baseStart_463689 baseEnd_463689 := by
    simpa [prefixWord, tailWord_463689, baseEnd_463689] using wordTrace_append hprefix tailTrace_463689
  have hstable : (prefixWord ++ tailWord_463689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463689).length < 2 ^ (prefixWord ++ tailWord_463689).sum := by decide
  have hdescent : baseEnd_463689 < baseStart_463689 := by decide
  rcases family_descends (prefixWord ++ tailWord_463689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463779 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3]
def baseStart_463779 : Nat := 118140960795 + 463779 * 2 ^ 59
def prefixEnd_463779 : Nat := 4983230072969 + 3 ^ 40 * 463779 * 2
def baseEnd_463779 : Nat := 238141544461646196229625

theorem tailTrace_463779 : CollatzResearch.WordTrace tailWord_463779 prefixEnd_463779 238141544461646196229625 := by
  unfold tailWord_463779
  simp only [CollatzResearch.WordTrace]
  refine ⟨16915409786815364992306391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11276939857876909994870927 16915409786815364992306391)
  ·
    refine ⟨25373114680223047488459587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16915409786815364992306391 25373114680223047488459587)
    ·
      refine ⟨38059672020334571232689381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25373114680223047488459587 38059672020334571232689381)
      ·
        refine ⟨7136188503812732106129259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38059672020334571232689381 7136188503812732106129259)
        ·
          refine ⟨10704282755719098159193889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136188503812732106129259 10704282755719098159193889)
          ·
            refine ⟨8028212066789323619395417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10704282755719098159193889 8028212066789323619395417)
            ·
              refine ⟨6021159050091992714546563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028212066789323619395417 6021159050091992714546563)
              ·
                refine ⟨9031738575137989071819845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021159050091992714546563 9031738575137989071819845)
                ·
                  refine ⟨1693450982838372950966221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9031738575137989071819845 1693450982838372950966221)
                  ·
                    refine ⟨635044118564389856612333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693450982838372950966221 635044118564389856612333)
                    ·
                      refine ⟨238141544461646196229625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635044118564389856612333 238141544461646196229625)
                      ·
                        rfl

theorem cell23_463779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_463779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463779 prefixEnd_463779 := by exact prefixLift 463779
  have htrace : WordTrace (prefixWord ++ tailWord_463779) baseStart_463779 baseEnd_463779 := by
    simpa [prefixWord, tailWord_463779, baseEnd_463779] using wordTrace_append hprefix tailTrace_463779
  have hstable : (prefixWord ++ tailWord_463779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463779).length < 2 ^ (prefixWord ++ tailWord_463779).sum := by decide
  have hdescent : baseEnd_463779 < baseStart_463779 := by decide
  rcases family_descends (prefixWord ++ tailWord_463779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463826 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_463826 : Nat := 118140960795 + 463826 * 2 ^ 59
def prefixEnd_463826 : Nat := 4983230072969 + 3 ^ 40 * 463826 * 2
def baseEnd_463826 : Nat := 238165678052407512341909

theorem tailTrace_463826 : CollatzResearch.WordTrace tailWord_463826 prefixEnd_463826 238165678052407512341909 := by
  unfold tailWord_463826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229281004411273004816833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11278082678430061346178221 4229281004411273004816833)
  ·
    refine ⟨3171960753308454753612625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4229281004411273004816833 3171960753308454753612625)
    ·
      refine ⟨2378970564981341065209469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3171960753308454753612625 2378970564981341065209469)
      ·
        refine ⟨892113961868002899453551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2378970564981341065209469 892113961868002899453551)
        ·
          refine ⟨1338170942802004349180327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892113961868002899453551 1338170942802004349180327)
          ·
            refine ⟨2007256414203006523770491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338170942802004349180327 2007256414203006523770491)
            ·
              refine ⟨3010884621304509785655737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007256414203006523770491 3010884621304509785655737)
              ·
                refine ⟨2258163465978382339241803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010884621304509785655737 2258163465978382339241803)
                ·
                  refine ⟨3387245198967573508862705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258163465978382339241803 3387245198967573508862705)
                  ·
                    refine ⟨2540433899225680131647029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387245198967573508862705 2540433899225680131647029)
                    ·
                      refine ⟨238165678052407512341909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2540433899225680131647029 238165678052407512341909)
                      ·
                        rfl

theorem cell23_463826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_463826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463826 prefixEnd_463826 := by exact prefixLift 463826
  have htrace : WordTrace (prefixWord ++ tailWord_463826) baseStart_463826 baseEnd_463826 := by
    simpa [prefixWord, tailWord_463826, baseEnd_463826] using wordTrace_append hprefix tailTrace_463826
  have hstable : (prefixWord ++ tailWord_463826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463826).length < 2 ^ (prefixWord ++ tailWord_463826).sum := by decide
  have hdescent : baseEnd_463826 < baseStart_463826 := by decide
  rcases family_descends (prefixWord ++ tailWord_463826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463873 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_463873 : Nat := 118140960795 + 463873 * 2 ^ 59
def prefixEnd_463873 : Nat := 4983230072969 + 3 ^ 40 * 463873 * 2
def baseEnd_463873 : Nat := 238189811643168828454193

theorem tailTrace_463873 : CollatzResearch.WordTrace tailWord_463873 prefixEnd_463873 238189811643168828454193 := by
  unfold tailWord_463873
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918838248474819046228273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11279225498983212697485515 16918838248474819046228273)
  ·
    refine ⟨12689128686356114284671205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16918838248474819046228273 12689128686356114284671205)
    ·
      refine ⟨2379211628691771428375851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12689128686356114284671205 2379211628691771428375851)
      ·
        refine ⟨3568817443037657142563777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379211628691771428375851 3568817443037657142563777)
        ·
          refine ⟨2676613082278242856922833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568817443037657142563777 2676613082278242856922833)
          ·
            refine ⟨2007459811708682142692125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676613082278242856922833 2007459811708682142692125)
            ·
              refine ⟨752797429390755803509547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007459811708682142692125 752797429390755803509547)
              ·
                refine ⟨1129196144086133705264321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752797429390755803509547 1129196144086133705264321)
                ·
                  refine ⟨846897108064600278948241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129196144086133705264321 846897108064600278948241)
                  ·
                    refine ⟨635172831048450209211181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846897108064600278948241 635172831048450209211181)
                    ·
                      refine ⟨238189811643168828454193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635172831048450209211181 238189811643168828454193)
                      ·
                        rfl

theorem cell23_463873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_463873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463873 prefixEnd_463873 := by exact prefixLift 463873
  have htrace : WordTrace (prefixWord ++ tailWord_463873) baseStart_463873 baseEnd_463873 := by
    simpa [prefixWord, tailWord_463873, baseEnd_463873] using wordTrace_append hprefix tailTrace_463873
  have hstable : (prefixWord ++ tailWord_463873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463873).length < 2 ^ (prefixWord ++ tailWord_463873).sum := by decide
  have hdescent : baseEnd_463873 < baseStart_463873 := by decide
  rcases family_descends (prefixWord ++ tailWord_463873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463880 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 1, 4]
def baseStart_463880 : Nat := 118140960795 + 463880 * 2 ^ 59
def prefixEnd_463880 : Nat := 4983230072969 + 3 ^ 40 * 463880 * 2
def baseEnd_463880 : Nat := 79397802002583433688887

theorem tailTrace_463880 : CollatzResearch.WordTrace tailWord_463880 prefixEnd_463880 79397802002583433688887 := by
  unfold tailWord_463880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459546779724729620866547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11279395706299639494488729 8459546779724729620866547)
  ·
    refine ⟨12689320169587094431299821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8459546779724729620866547 12689320169587094431299821)
    ·
      refine ⟨4758495063595160411737433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12689320169587094431299821 4758495063595160411737433)
      ·
        refine ⟨3568871297696370308803075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758495063595160411737433 3568871297696370308803075)
        ·
          refine ⟨5353306946544555463204613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568871297696370308803075 5353306946544555463204613)
          ·
            refine ⟨1003745052477104149350865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5353306946544555463204613 1003745052477104149350865)
            ·
              refine ⟨752808789357828112013149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003745052477104149350865 752808789357828112013149)
              ·
                refine ⟨282303296009185542004931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752808789357828112013149 282303296009185542004931)
                ·
                  refine ⟨423454944013778313007397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282303296009185542004931 423454944013778313007397)
                  ·
                    refine ⟨79397802002583433688887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423454944013778313007397 79397802002583433688887)
                    ·
                      rfl

theorem cell23_463880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_463880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463880 prefixEnd_463880 := by exact prefixLift 463880
  have htrace : WordTrace (prefixWord ++ tailWord_463880) baseStart_463880 baseEnd_463880 := by
    simpa [prefixWord, tailWord_463880, baseEnd_463880] using wordTrace_append hprefix tailTrace_463880
  have hstable : (prefixWord ++ tailWord_463880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463880).length < 2 ^ (prefixWord ++ tailWord_463880).sum := by decide
  have hdescent : baseEnd_463880 < baseStart_463880 := by decide
  rcases family_descends (prefixWord ++ tailWord_463880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463893 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 6]
def baseStart_463893 : Nat := 118140960795 + 463893 * 2 ^ 59
def prefixEnd_463893 : Nat := 4983230072969 + 3 ^ 40 * 463893 * 2
def baseEnd_463893 : Nat := 26466675695139861133789

theorem tailTrace_463893 : CollatzResearch.WordTrace tailWord_463893 prefixEnd_463893 26466675695139861133789 := by
  unfold tailWord_463893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919567708402362461956333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11279711805601574974637555 16919567708402362461956333)
  ·
    refine ⟨6344837890650885923233625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16919567708402362461956333 6344837890650885923233625)
    ·
      refine ⟨4758628417988164442425219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344837890650885923233625 4758628417988164442425219)
      ·
        refine ⟨7137942626982246663637829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758628417988164442425219 7137942626982246663637829)
        ·
          refine ⟨1338364242559171249432093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7137942626982246663637829 1338364242559171249432093)
          ·
            refine ⟨501886590959689218537035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338364242559171249432093 501886590959689218537035)
            ·
              refine ⟨752829886439533827805553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501886590959689218537035 752829886439533827805553)
              ·
                refine ⟨564622414829650370854165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752829886439533827805553 564622414829650370854165)
                ·
                  refine ⟨26466675695139861133789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 564622414829650370854165 26466675695139861133789)
                  ·
                    rfl

theorem cell23_463893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_463893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463893 prefixEnd_463893 := by exact prefixLift 463893
  have htrace : WordTrace (prefixWord ++ tailWord_463893) baseStart_463893 baseEnd_463893 := by
    simpa [prefixWord, tailWord_463893, baseEnd_463893] using wordTrace_append hprefix tailTrace_463893
  have hstable : (prefixWord ++ tailWord_463893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463893).length < 2 ^ (prefixWord ++ tailWord_463893).sum := by decide
  have hdescent : baseEnd_463893 < baseStart_463893 := by decide
  rcases family_descends (prefixWord ++ tailWord_463893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463903 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 3]
def baseStart_463903 : Nat := 118140960795 + 463903 * 2 ^ 59
def prefixEnd_463903 : Nat := 4983230072969 + 3 ^ 40 * 463903 * 2
def baseEnd_463903 : Nat := 238205216062803711079055

theorem tailTrace_463903 : CollatzResearch.WordTrace tailWord_463903 prefixEnd_463903 238205216062803711079055 := by
  unfold tailWord_463903
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919932438366134169820363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11279954958910756113213575 16919932438366134169820363)
  ·
    refine ⟨25379898657549201254730545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16919932438366134169820363 25379898657549201254730545)
    ·
      refine ⟨19034923993161900941047909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25379898657549201254730545 19034923993161900941047909)
      ·
        refine ⟨3569048248717856426446483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19034923993161900941047909 3569048248717856426446483)
        ·
          refine ⟨5353572373076784639669725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569048248717856426446483 5353572373076784639669725)
          ·
            refine ⟨2007589639903794239876147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5353572373076784639669725 2007589639903794239876147)
            ·
              refine ⟨3011384459855691359814221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007589639903794239876147 3011384459855691359814221)
              ·
                refine ⟨1129269172445884259930333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011384459855691359814221 1129269172445884259930333)
                ·
                  refine ⟨423475939667206597473875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129269172445884259930333 423475939667206597473875)
                  ·
                    refine ⟨635213909500809896210813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 423475939667206597473875 635213909500809896210813)
                    ·
                      refine ⟨238205216062803711079055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635213909500809896210813 238205216062803711079055)
                      ·
                        rfl

theorem cell23_463903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_463903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463903 prefixEnd_463903 := by exact prefixLift 463903
  have htrace : WordTrace (prefixWord ++ tailWord_463903) baseStart_463903 baseEnd_463903 := by
    simpa [prefixWord, tailWord_463903, baseEnd_463903] using wordTrace_append hprefix tailTrace_463903
  have hstable : (prefixWord ++ tailWord_463903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463903).length < 2 ^ (prefixWord ++ tailWord_463903).sum := by decide
  have hdescent : baseEnd_463903 < baseStart_463903 := by decide
  rcases family_descends (prefixWord ++ tailWord_463903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463936 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_463936 : Nat := 118140960795 + 463936 * 2 ^ 59
def prefixEnd_463936 : Nat := 4983230072969 + 3 ^ 40 * 463936 * 2
def baseEnd_463936 : Nat := 79407386974800693988801

theorem tailTrace_463936 : CollatzResearch.WordTrace tailWord_463936 prefixEnd_463936 79407386974800693988801 := by
  unfold tailWord_463936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460568023623290402885831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11280757364831053870514441 8460568023623290402885831)
  ·
    refine ⟨12690852035434935604328747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8460568023623290402885831 12690852035434935604328747)
    ·
      refine ⟨19036278053152403406493121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12690852035434935604328747 19036278053152403406493121)
      ·
        refine ⟨14277208539864302554869841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19036278053152403406493121 14277208539864302554869841)
        ·
          refine ⟨10707906404898226916152381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14277208539864302554869841 10707906404898226916152381)
          ·
            refine ⟨4015464901836835093557143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10707906404898226916152381 4015464901836835093557143)
            ·
              refine ⟨6023197352755252640335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015464901836835093557143 6023197352755252640335715)
              ·
                refine ⟨9034796029132878960503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023197352755252640335715 9034796029132878960503573)
                ·
                  refine ⟨423506063865603701273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9034796029132878960503573 423506063865603701273605)
                  ·
                    refine ⟨79407386974800693988801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423506063865603701273605 79407386974800693988801)
                    ·
                      rfl

theorem cell23_463936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_463936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463936 prefixEnd_463936 := by exact prefixLift 463936
  have htrace : WordTrace (prefixWord ++ tailWord_463936) baseStart_463936 baseEnd_463936 := by
    simpa [prefixWord, tailWord_463936, baseEnd_463936] using wordTrace_append hprefix tailTrace_463936
  have hstable : (prefixWord ++ tailWord_463936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463936).length < 2 ^ (prefixWord ++ tailWord_463936).sum := by decide
  have hdescent : baseEnd_463936 < baseStart_463936 := by decide
  rcases family_descends (prefixWord ++ tailWord_463936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463943 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_463943 : Nat := 118140960795 + 463943 * 2 ^ 59
def prefixEnd_463943 : Nat := 4983230072969 + 3 ^ 40 * 463943 * 2
def baseEnd_463943 : Nat := 238225755288983554578871

theorem tailTrace_463943 : CollatzResearch.WordTrace tailWord_463943 prefixEnd_463943 238225755288983554578871 := by
  unfold tailWord_463943
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921391358221221001276483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11280927572147480667517655 16921391358221221001276483)
  ·
    refine ⟨25382087037331831501914725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16921391358221221001276483 25382087037331831501914725)
    ·
      refine ⟨4759141319499718406609011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25382087037331831501914725 4759141319499718406609011)
      ·
        refine ⟨7138711979249577609913517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759141319499718406609011 7138711979249577609913517)
        ·
          refine ⟨2677016992218591603717569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7138711979249577609913517 2677016992218591603717569)
          ·
            refine ⟨2007762744163943702788177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677016992218591603717569 2007762744163943702788177)
            ·
              refine ⟨1505822058122957777091133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007762744163943702788177 1505822058122957777091133)
              ·
                refine ⟨564683271796109166409175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505822058122957777091133 564683271796109166409175)
                ·
                  refine ⟨847024907694163749613763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564683271796109166409175 847024907694163749613763)
                  ·
                    refine ⟨1270537361541245624420645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847024907694163749613763 1270537361541245624420645)
                    ·
                      refine ⟨238225755288983554578871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1270537361541245624420645 238225755288983554578871)
                      ·
                        rfl

theorem cell23_463943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_463943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463943 prefixEnd_463943 := by exact prefixLift 463943
  have htrace : WordTrace (prefixWord ++ tailWord_463943) baseStart_463943 baseEnd_463943 := by
    simpa [prefixWord, tailWord_463943, baseEnd_463943] using wordTrace_append hprefix tailTrace_463943
  have hstable : (prefixWord ++ tailWord_463943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463943).length < 2 ^ (prefixWord ++ tailWord_463943).sum := by decide
  have hdescent : baseEnd_463943 < baseStart_463943 := by decide
  rcases family_descends (prefixWord ++ tailWord_463943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463946 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_463946 : Nat := 118140960795 + 463946 * 2 ^ 59
def prefixEnd_463946 : Nat := 4983230072969 + 3 ^ 40 * 463946 * 2
def baseEnd_463946 : Nat := 238227295730947042841357

theorem tailTrace_463946 : CollatzResearch.WordTrace tailWord_463946 prefixEnd_463946 238227295730947042841357 := by
  unfold tailWord_463946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230375194302588128408923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11281000518140235009090461 4230375194302588128408923)
  ·
    refine ⟨6345562791453882192613385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230375194302588128408923 6345562791453882192613385)
    ·
      refine ⟨4759172093590411644460039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6345562791453882192613385 4759172093590411644460039)
      ·
        refine ⟨7138758140385617466690059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759172093590411644460039 7138758140385617466690059)
        ·
          refine ⟨10708137210578426200035089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138758140385617466690059 10708137210578426200035089)
          ·
            refine ⟨8031102907933819650026317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10708137210578426200035089 8031102907933819650026317)
            ·
              refine ⟨3011663590475182368759869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8031102907933819650026317 3011663590475182368759869)
              ·
                refine ⟨1129373846428193388284951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011663590475182368759869 1129373846428193388284951)
                ·
                  refine ⟨1694060769642290082427427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129373846428193388284951 1694060769642290082427427)
                  ·
                    refine ⟨2541091154463435123641141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1694060769642290082427427 2541091154463435123641141)
                    ·
                      refine ⟨238227295730947042841357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2541091154463435123641141 238227295730947042841357)
                      ·
                        rfl

theorem cell23_463946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_463946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463946 prefixEnd_463946 := by exact prefixLift 463946
  have htrace : WordTrace (prefixWord ++ tailWord_463946) baseStart_463946 baseEnd_463946 := by
    simpa [prefixWord, tailWord_463946, baseEnd_463946] using wordTrace_append hprefix tailTrace_463946
  have hstable : (prefixWord ++ tailWord_463946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463946).length < 2 ^ (prefixWord ++ tailWord_463946).sum := by decide
  have hdescent : baseEnd_463946 < baseStart_463946 := by decide
  rcases family_descends (prefixWord ++ tailWord_463946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463954 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_463954 : Nat := 118140960795 + 463954 * 2 ^ 59
def prefixEnd_463954 : Nat := 4983230072969 + 3 ^ 40 * 463954 * 2
def baseEnd_463954 : Nat := 238231403576183011541321

theorem tailTrace_463954 : CollatzResearch.WordTrace tailWord_463954 prefixEnd_463954 238231403576183011541321 := by
  unfold tailWord_463954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230448140295342469981729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11281195040787579919951277 4230448140295342469981729)
  ·
    refine ⟨3172836105221506852486297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4230448140295342469981729 3172836105221506852486297)
    ·
      refine ⟨2379627078916130139364723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3172836105221506852486297 2379627078916130139364723)
      ·
        refine ⟨3569440618374195209047085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379627078916130139364723 3569440618374195209047085)
        ·
          refine ⟨1338540231890323203392657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3569440618374195209047085 1338540231890323203392657)
          ·
            refine ⟨1003905173917742402544493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338540231890323203392657 1003905173917742402544493)
            ·
              refine ⟨376464440219153400954185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1003905173917742402544493 376464440219153400954185)
              ·
                refine ⟨282348330164365050715639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376464440219153400954185 282348330164365050715639)
                ·
                  refine ⟨423522495246547576073459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282348330164365050715639 423522495246547576073459)
                  ·
                    refine ⟨635283742869821364110189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 423522495246547576073459 635283742869821364110189)
                    ·
                      refine ⟨238231403576183011541321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635283742869821364110189 238231403576183011541321)
                      ·
                        rfl

theorem cell23_463954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_463954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463954 prefixEnd_463954 := by exact prefixLift 463954
  have htrace : WordTrace (prefixWord ++ tailWord_463954) baseStart_463954 baseEnd_463954 := by
    simpa [prefixWord, tailWord_463954, baseEnd_463954] using wordTrace_append hprefix tailTrace_463954
  have hstable : (prefixWord ++ tailWord_463954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463954).length < 2 ^ (prefixWord ++ tailWord_463954).sum := by decide
  have hdescent : baseEnd_463954 < baseStart_463954 := by decide
  rcases family_descends (prefixWord ++ tailWord_463954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463956 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_463956 : Nat := 118140960795 + 463956 * 2 ^ 59
def prefixEnd_463956 : Nat := 4983230072969 + 3 ^ 40 * 463956 * 2
def baseEnd_463956 : Nat := 238232430537492003716311

theorem tailTrace_463956 : CollatzResearch.WordTrace tailWord_463956 prefixEnd_463956 238232430537492003716311 := by
  unfold tailWord_463956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460932753587062110749861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11281243671449416147666481 8460932753587062110749861)
  ·
    refine ⟨1586424891297574145765599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8460932753587062110749861 1586424891297574145765599)
    ·
      refine ⟨2379637336946361218648399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586424891297574145765599 2379637336946361218648399)
      ·
        refine ⟨3569456005419541827972599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379637336946361218648399 3569456005419541827972599)
        ·
          refine ⟨5354184008129312741958899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569456005419541827972599 5354184008129312741958899)
          ·
            refine ⟨8031276012193969112938349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354184008129312741958899 8031276012193969112938349)
            ·
              refine ⟨3011728504572738417351881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8031276012193969112938349 3011728504572738417351881)
              ·
                refine ⟨2258796378429553813013911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011728504572738417351881 2258796378429553813013911)
                ·
                  refine ⟨3388194567644330719520867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258796378429553813013911 3388194567644330719520867)
                  ·
                    refine ⟨5082291851466496079281301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388194567644330719520867 5082291851466496079281301)
                    ·
                      refine ⟨238232430537492003716311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5082291851466496079281301 238232430537492003716311)
                      ·
                        rfl

theorem cell23_463956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_463956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_463956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_463956 prefixEnd_463956 := by exact prefixLift 463956
  have htrace : WordTrace (prefixWord ++ tailWord_463956) baseStart_463956 baseEnd_463956 := by
    simpa [prefixWord, tailWord_463956, baseEnd_463956] using wordTrace_append hprefix tailTrace_463956
  have hstable : (prefixWord ++ tailWord_463956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463956).length < 2 ^ (prefixWord ++ tailWord_463956).sum := by decide
  have hdescent : baseEnd_463956 < baseStart_463956 := by decide
  rcases family_descends (prefixWord ++ tailWord_463956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464050 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_464050 : Nat := 118140960795 + 464050 * 2 ^ 59
def prefixEnd_464050 : Nat := 4983230072969 + 3 ^ 40 * 464050 * 2
def baseEnd_464050 : Nat := 238280697719014635940879

theorem tailTrace_464050 : CollatzResearch.WordTrace tailWord_464050 prefixEnd_464050 238280697719014635940879 := by
  unfold tailWord_464050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231323492208394568855401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11283529312555718850281069 4231323492208394568855401)
  ·
    refine ⟨3173492619156295926641551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4231323492208394568855401 3173492619156295926641551)
    ·
      refine ⟨4760238928734443889962327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173492619156295926641551 4760238928734443889962327)
      ·
        refine ⟨7140358393101665834943491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760238928734443889962327 7140358393101665834943491)
        ·
          refine ⟨10710537589652498752415237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140358393101665834943491 10710537589652498752415237)
          ·
            refine ⟨2008225798059843516077857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10710537589652498752415237 2008225798059843516077857)
            ·
              refine ⟨1506169348544882637058393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008225798059843516077857 1506169348544882637058393)
              ·
                refine ⟨1129627011408661977793795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506169348544882637058393 1129627011408661977793795)
                ·
                  refine ⟨1694440517112992966690693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129627011408661977793795 1694440517112992966690693)
                  ·
                    refine ⟨317707596958686181254505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694440517112992966690693 317707596958686181254505)
                    ·
                      refine ⟨238280697719014635940879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317707596958686181254505 238280697719014635940879)
                      ·
                        rfl

theorem cell23_464050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_464050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464050 prefixEnd_464050 := by exact prefixLift 464050
  have htrace : WordTrace (prefixWord ++ tailWord_464050) baseStart_464050 baseEnd_464050 := by
    simpa [prefixWord, tailWord_464050, baseEnd_464050] using wordTrace_append hprefix tailTrace_464050
  have hstable : (prefixWord ++ tailWord_464050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464050).length < 2 ^ (prefixWord ++ tailWord_464050).sum := by decide
  have hdescent : baseEnd_464050 < baseStart_464050 := by decide
  rcases family_descends (prefixWord ++ tailWord_464050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464157 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_464157 : Nat := 118140960795 + 464157 * 2 ^ 59
def prefixEnd_464157 : Nat := 4983230072969 + 3 ^ 40 * 464157 * 2
def baseEnd_464157 : Nat := 238335640149045717302887

theorem tailTrace_464157 : CollatzResearch.WordTrace tailWord_464157 prefixEnd_464157 238335640149045717302887 := by
  unfold tailWord_464157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929196579445935549566725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11286131052963957033044483 16929196579445935549566725)
  ·
    refine ⟨3174224358646112915543761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16929196579445935549566725 3174224358646112915543761)
    ·
      refine ⟨2380668268984584686657821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3174224358646112915543761 2380668268984584686657821)
      ·
        refine ⟨892750600869219257496683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2380668268984584686657821 892750600869219257496683)
        ·
          refine ⟨1339125901303828886245025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892750600869219257496683 1339125901303828886245025)
          ·
            refine ⟨1004344425977871664683769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339125901303828886245025 1004344425977871664683769)
            ·
              refine ⟨753258319483403748512827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004344425977871664683769 753258319483403748512827)
              ·
                refine ⟨1129887479225105622769241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753258319483403748512827 1129887479225105622769241)
                ·
                  refine ⟨847415609418829217076931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129887479225105622769241 847415609418829217076931)
                  ·
                    refine ⟨1271123414128243825615397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847415609418829217076931 1271123414128243825615397)
                    ·
                      refine ⟨238335640149045717302887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1271123414128243825615397 238335640149045717302887)
                      ·
                        rfl

theorem cell23_464157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_464157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464157 prefixEnd_464157 := by exact prefixLift 464157
  have htrace : WordTrace (prefixWord ++ tailWord_464157) baseStart_464157 baseEnd_464157 := by
    simpa [prefixWord, tailWord_464157, baseEnd_464157] using wordTrace_append hprefix tailTrace_464157
  have hstable : (prefixWord ++ tailWord_464157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464157).length < 2 ^ (prefixWord ++ tailWord_464157).sum := by decide
  have hdescent : baseEnd_464157 < baseStart_464157 := by decide
  rcases family_descends (prefixWord ++ tailWord_464157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464200 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_464200 : Nat := 118140960795 + 464200 * 2 ^ 59
def prefixEnd_464200 : Nat := 4983230072969 + 3 ^ 40 * 464200 * 2
def baseEnd_464200 : Nat := 238357719817189049065189

theorem tailTrace_464200 : CollatzResearch.WordTrace tailWord_464200 prefixEnd_464200 238357719817189049065189 := by
  unfold tailWord_464200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465382459145076946691027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11287176612193435928921369 8465382459145076946691027)
  ·
    refine ⟨12698073688717615420036541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465382459145076946691027 12698073688717615420036541)
    ·
      refine ⟨4761777633269105782513703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12698073688717615420036541 4761777633269105782513703)
      ·
        refine ⟨7142666449903658673770555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761777633269105782513703 7142666449903658673770555)
        ·
          refine ⟨10713999674855488010655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142666449903658673770555 10713999674855488010655833)
          ·
            refine ⟨8035499756141616007991875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10713999674855488010655833 8035499756141616007991875)
            ·
              refine ⟨12053249634212424011987813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035499756141616007991875 12053249634212424011987813)
              ·
                refine ⟨2259984306414829502247715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12053249634212424011987813 2259984306414829502247715)
                ·
                  refine ⟨3389976459622244253371573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259984306414829502247715 3389976459622244253371573)
                  ·
                    refine ⟨317810293089585398753585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3389976459622244253371573 317810293089585398753585)
                    ·
                      refine ⟨238357719817189049065189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317810293089585398753585 238357719817189049065189)
                      ·
                        rfl

theorem cell23_464200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_464200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464200 prefixEnd_464200 := by exact prefixLift 464200
  have htrace : WordTrace (prefixWord ++ tailWord_464200) baseStart_464200 baseEnd_464200 := by
    simpa [prefixWord, tailWord_464200, baseEnd_464200] using wordTrace_append hprefix tailTrace_464200
  have hstable : (prefixWord ++ tailWord_464200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464200).length < 2 ^ (prefixWord ++ tailWord_464200).sum := by decide
  have hdescent : baseEnd_464200 < baseStart_464200 := by decide
  rcases family_descends (prefixWord ++ tailWord_464200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464210 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_464210 : Nat := 118140960795 + 464210 * 2 ^ 59
def prefixEnd_464210 : Nat := 4983230072969 + 3 ^ 40 * 464210 * 2
def baseEnd_464210 : Nat := 79454284874578003313381

theorem tailTrace_464210 : CollatzResearch.WordTrace tailWord_464210 prefixEnd_464210 79454284874578003313381 := by
  unfold tailWord_464210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232782412063481400311521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11287419765502617067497389 4232782412063481400311521)
  ·
    refine ⟨3174586809047611050233641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4232782412063481400311521 3174586809047611050233641)
    ·
      refine ⟨2380940106785708287675231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3174586809047611050233641 2380940106785708287675231)
      ·
        refine ⟨3571410160178562431512847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380940106785708287675231 3571410160178562431512847)
        ·
          refine ⟨5357115240267843647269271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571410160178562431512847 5357115240267843647269271)
          ·
            refine ⟨8035672860401765470903907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357115240267843647269271 8035672860401765470903907)
            ·
              refine ⟨12053509290602648206355861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035672860401765470903907 12053509290602648206355861)
              ·
                refine ⟨565008247996999134672931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12053509290602648206355861 565008247996999134672931)
                ·
                  refine ⟨847512371995498702009397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565008247996999134672931 847512371995498702009397)
                  ·
                    refine ⟨79454284874578003313381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 847512371995498702009397 79454284874578003313381)
                    ·
                      rfl

theorem cell23_464210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_464210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464210 prefixEnd_464210 := by exact prefixLift 464210
  have htrace : WordTrace (prefixWord ++ tailWord_464210) baseStart_464210 baseEnd_464210 := by
    simpa [prefixWord, tailWord_464210, baseEnd_464210] using wordTrace_append hprefix tailTrace_464210
  have hstable : (prefixWord ++ tailWord_464210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464210).length < 2 ^ (prefixWord ++ tailWord_464210).sum := by decide
  have hdescent : baseEnd_464210 < baseStart_464210 := by decide
  rcases family_descends (prefixWord ++ tailWord_464210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464217 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 2, 3, 2]
def baseStart_464217 : Nat := 118140960795 + 464217 * 2 ^ 59
def prefixEnd_464217 : Nat := 4983230072969 + 3 ^ 40 * 464217 * 2
def baseEnd_464217 : Nat := 238366448988315482552611

theorem tailTrace_464217 : CollatzResearch.WordTrace tailWord_464217 prefixEnd_464217 238366448988315482552611 := by
  unfold tailWord_464217
  simp only [CollatzResearch.WordTrace]
  refine ⟨16931384959228565796750905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11287589972819043864500603 16931384959228565796750905)
  ·
    refine ⟨12698538719421424347563179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16931384959228565796750905 12698538719421424347563179)
    ·
      refine ⟨19047808079132136521344769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698538719421424347563179 19047808079132136521344769)
      ·
        refine ⟨14285856059349102391008577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19047808079132136521344769 14285856059349102391008577)
        ·
          refine ⟨10714392044511826793256433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14285856059349102391008577 10714392044511826793256433)
          ·
            refine ⟨8035794033383870094942325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714392044511826793256433 8035794033383870094942325)
            ·
              refine ⟨753355690629737821400843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8035794033383870094942325 753355690629737821400843)
              ·
                refine ⟨1130033535944606732101265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753355690629737821400843 1130033535944606732101265)
                ·
                  refine ⟨847525151958455049075949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130033535944606732101265 847525151958455049075949)
                  ·
                    refine ⟨317821931984420643403481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847525151958455049075949 317821931984420643403481)
                    ·
                      refine ⟨238366448988315482552611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317821931984420643403481 238366448988315482552611)
                      ·
                        rfl

theorem cell23_464217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_464217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464217 prefixEnd_464217 := by exact prefixLift 464217
  have htrace : WordTrace (prefixWord ++ tailWord_464217) baseStart_464217 baseEnd_464217 := by
    simpa [prefixWord, tailWord_464217, baseEnd_464217] using wordTrace_append hprefix tailTrace_464217
  have hstable : (prefixWord ++ tailWord_464217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464217).length < 2 ^ (prefixWord ++ tailWord_464217).sum := by decide
  have hdescent : baseEnd_464217 < baseStart_464217 := by decide
  rcases family_descends (prefixWord ++ tailWord_464217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464224 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 1, 1, 3]
def baseStart_464224 : Nat := 118140960795 + 464224 * 2 ^ 59
def prefixEnd_464224 : Nat := 4983230072969 + 3 ^ 40 * 464224 * 2
def baseEnd_464224 : Nat := 238370043352896955165079

theorem tailTrace_464224 : CollatzResearch.WordTrace tailWord_464224 prefixEnd_464224 238370043352896955165079 := by
  unfold tailWord_464224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465820135101602996127863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11287760180135470661503817 8465820135101602996127863)
  ·
    refine ⟨12698730202652404494191795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465820135101602996127863 12698730202652404494191795)
    ·
      refine ⟨19048095303978606741287693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698730202652404494191795 19048095303978606741287693)
      ·
        refine ⟨7143035738991977527982885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19048095303978606741287693 7143035738991977527982885)
        ·
          refine ⟨1339319201060995786496791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7143035738991977527982885 1339319201060995786496791)
          ·
            refine ⟨2008978801591493679745187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339319201060995786496791 2008978801591493679745187)
            ·
              refine ⟨3013468202387240519617781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008978801591493679745187 3013468202387240519617781)
              ·
                refine ⟨282512643973803798714167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3013468202387240519617781 282512643973803798714167)
                ·
                  refine ⟨423768965960705698071251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282512643973803798714167 423768965960705698071251)
                  ·
                    refine ⟨635653448941058547106877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 423768965960705698071251 635653448941058547106877)
                    ·
                      refine ⟨238370043352896955165079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635653448941058547106877 238370043352896955165079)
                      ·
                        rfl

theorem cell23_464224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_464224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464224 prefixEnd_464224 := by exact prefixLift 464224
  have htrace : WordTrace (prefixWord ++ tailWord_464224) baseStart_464224 baseEnd_464224 := by
    simpa [prefixWord, tailWord_464224, baseEnd_464224] using wordTrace_append hprefix tailTrace_464224
  have hstable : (prefixWord ++ tailWord_464224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464224).length < 2 ^ (prefixWord ++ tailWord_464224).sum := by decide
  have hdescent : baseEnd_464224 < baseStart_464224 := by decide
  rcases family_descends (prefixWord ++ tailWord_464224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464227 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 1, 5]
def baseStart_464227 : Nat := 118140960795 + 464227 * 2 ^ 59
def prefixEnd_464227 : Nat := 4983230072969 + 3 ^ 40 * 464227 * 2
def baseEnd_464227 : Nat := 79457194598286814475855

theorem tailTrace_464227 : CollatzResearch.WordTrace tailWord_464227 prefixEnd_464227 79457194598286814475855 := by
  unfold tailWord_464227
  simp only [CollatzResearch.WordTrace]
  refine ⟨16931749689192337504614935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11287833126128225003076623 16931749689192337504614935)
  ·
    refine ⟨25397624533788506256922403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16931749689192337504614935 25397624533788506256922403)
    ·
      refine ⟨38096436800682759385383605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25397624533788506256922403 38096436800682759385383605)
      ·
        refine ⟨3571540950064008692379713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38096436800682759385383605 3571540950064008692379713)
        ·
          refine ⟨2678655712548006519284785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571540950064008692379713 2678655712548006519284785)
          ·
            refine ⟨2008991784411004889463589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678655712548006519284785 2008991784411004889463589)
            ·
              refine ⟨376685959577063416774423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2008991784411004889463589 376685959577063416774423)
              ·
                refine ⟨565028939365595125161635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376685959577063416774423 565028939365595125161635)
                ·
                  refine ⟨847543409048392687742453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565028939365595125161635 847543409048392687742453)
                  ·
                    refine ⟨79457194598286814475855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 847543409048392687742453 79457194598286814475855)
                    ·
                      rfl

theorem cell23_464227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 1, 5].length) (baseStart_464227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464227 prefixEnd_464227 := by exact prefixLift 464227
  have htrace : WordTrace (prefixWord ++ tailWord_464227) baseStart_464227 baseEnd_464227 := by
    simpa [prefixWord, tailWord_464227, baseEnd_464227] using wordTrace_append hprefix tailTrace_464227
  have hstable : (prefixWord ++ tailWord_464227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464227).length < 2 ^ (prefixWord ++ tailWord_464227).sum := by decide
  have hdescent : baseEnd_464227 < baseStart_464227 := by decide
  rcases family_descends (prefixWord ++ tailWord_464227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464240 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_464240 : Nat := 118140960795 + 464240 * 2 ^ 59
def prefixEnd_464240 : Nat := 4983230072969 + 3 ^ 40 * 464240 * 2
def baseEnd_464240 : Nat := 79459419681122964188335

theorem tailTrace_464240 : CollatzResearch.WordTrace tailWord_464240 prefixEnd_464240 79459419681122964188335 := by
  unfold tailWord_464240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466111919072620362419087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11288149225430160483225449 8466111919072620362419087)
  ·
    refine ⟨12699167878608930543628631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8466111919072620362419087 12699167878608930543628631)
    ·
      refine ⟨19048751817913395815442947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699167878608930543628631 19048751817913395815442947)
      ·
        refine ⟨28573127726870093723164421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048751817913395815442947 28573127726870093723164421)
        ·
          refine ⟨5357461448788142573093329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28573127726870093723164421 5357461448788142573093329)
          ·
            refine ⟨4018096086591106929819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357461448788142573093329 4018096086591106929819997)
            ·
              refine ⟨1506786032471665098682499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4018096086591106929819997 1506786032471665098682499)
              ·
                refine ⟨2260179048707497648023749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506786032471665098682499 2260179048707497648023749)
                ·
                  refine ⟨423783571632655809004453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260179048707497648023749 423783571632655809004453)
                  ·
                    refine ⟨79459419681122964188335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423783571632655809004453 79459419681122964188335)
                    ·
                      rfl

theorem cell23_464240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_464240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464240 prefixEnd_464240 := by exact prefixLift 464240
  have htrace : WordTrace (prefixWord ++ tailWord_464240) baseStart_464240 baseEnd_464240 := by
    simpa [prefixWord, tailWord_464240, baseEnd_464240] using wordTrace_append hprefix tailTrace_464240
  have hstable : (prefixWord ++ tailWord_464240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464240).length < 2 ^ (prefixWord ++ tailWord_464240).sum := by decide
  have hdescent : baseEnd_464240 < baseStart_464240 := by decide
  rcases family_descends (prefixWord ++ tailWord_464240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464253 : List Nat := [1, 4, 1, 1, 2, 2, 2, 10]
def baseStart_464253 : Nat := 118140960795 + 464253 * 2 ^ 59
def prefixEnd_464253 : Nat := 4983230072969 + 3 ^ 40 * 464253 * 2
def baseEnd_464253 : Nat := 8829071640439901544535

theorem tailTrace_464253 : CollatzResearch.WordTrace tailWord_464253 prefixEnd_464253 8829071640439901544535 := by
  unfold tailWord_464253
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932697987098143945061413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11288465324732095963374275 16932697987098143945061413)
  ·
    refine ⟨3174880872580901989699015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16932697987098143945061413 3174880872580901989699015)
    ·
      refine ⟨4762321308871352984548523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174880872580901989699015 4762321308871352984548523)
      ·
        refine ⟨7143481963307029476822785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762321308871352984548523 7143481963307029476822785)
        ·
          refine ⟨5357611472480272107617089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143481963307029476822785 5357611472480272107617089)
          ·
            refine ⟨4018208604360204080712817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357611472480272107617089 4018208604360204080712817)
            ·
              refine ⟨3013656453270153060534613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4018208604360204080712817 3013656453270153060534613)
              ·
                refine ⟨8829071640439901544535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3013656453270153060534613 8829071640439901544535)
                ·
                  rfl

theorem cell23_464253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 10].length) (baseStart_464253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464253 prefixEnd_464253 := by exact prefixLift 464253
  have htrace : WordTrace (prefixWord ++ tailWord_464253) baseStart_464253 baseEnd_464253 := by
    simpa [prefixWord, tailWord_464253, baseEnd_464253] using wordTrace_append hprefix tailTrace_464253
  have hstable : (prefixWord ++ tailWord_464253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464253).length < 2 ^ (prefixWord ++ tailWord_464253).sum := by decide
  have hdescent : baseEnd_464253 < baseStart_464253 := by decide
  rcases family_descends (prefixWord ++ tailWord_464253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464260 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_464260 : Nat := 118140960795 + 464260 * 2 ^ 59
def prefixEnd_464260 : Nat := 4983230072969 + 3 ^ 40 * 464260 * 2
def baseEnd_464260 : Nat := 238388528656458814314913

theorem tailTrace_464260 : CollatzResearch.WordTrace tailWord_464260 prefixEnd_464260 238388528656458814314913 := by
  unfold tailWord_464260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466476649036392070283117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11288635532048522760377489 8466476649036392070283117)
  ·
    refine ⟨3174928743388647026356169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8466476649036392070283117 3174928743388647026356169)
    ·
      refine ⟨2381196557541485269767127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3174928743388647026356169 2381196557541485269767127)
      ·
        refine ⟨3571794836312227904650691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381196557541485269767127 3571794836312227904650691)
        ·
          refine ⟨5357692254468341856976037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571794836312227904650691 5357692254468341856976037)
          ·
            refine ⟨1004567297712814098183007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5357692254468341856976037 1004567297712814098183007)
            ·
              refine ⟨1506850946569221147274511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004567297712814098183007 1506850946569221147274511)
              ·
                refine ⟨2260276419853831720911767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506850946569221147274511 2260276419853831720911767)
                ·
                  refine ⟨3390414629780747581367651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260276419853831720911767 3390414629780747581367651)
                  ·
                    refine ⟨5085621944671121372051477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390414629780747581367651 5085621944671121372051477)
                    ·
                      refine ⟨238388528656458814314913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5085621944671121372051477 238388528656458814314913)
                      ·
                        rfl

theorem cell23_464260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_464260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464260 prefixEnd_464260 := by exact prefixLift 464260
  have htrace : WordTrace (prefixWord ++ tailWord_464260) baseStart_464260 baseEnd_464260 := by
    simpa [prefixWord, tailWord_464260, baseEnd_464260] using wordTrace_append hprefix tailTrace_464260
  have hstable : (prefixWord ++ tailWord_464260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464260).length < 2 ^ (prefixWord ++ tailWord_464260).sum := by decide
  have hdescent : baseEnd_464260 < baseStart_464260 := by decide
  rcases family_descends (prefixWord ++ tailWord_464260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464264 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_464264 : Nat := 118140960795 + 464264 * 2 ^ 59
def prefixEnd_464264 : Nat := 4983230072969 + 3 ^ 40 * 464264 * 2
def baseEnd_464264 : Nat := 238390582579076798664895

theorem tailTrace_464264 : CollatzResearch.WordTrace tailWord_464264 prefixEnd_464264 238390582579076798664895 := by
  unfold tailWord_464264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466549595029146411855923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11288732793372195215807897 8466549595029146411855923)
  ·
    refine ⟨12699824392543719617783885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8466549595029146411855923 12699824392543719617783885)
    ·
      refine ⟨4762434147203894856668957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12699824392543719617783885 4762434147203894856668957)
      ·
        refine ⟨1785912805201460571250859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4762434147203894856668957 1785912805201460571250859)
        ·
          refine ⟨2678869207802190856876289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785912805201460571250859 2678869207802190856876289)
          ·
            refine ⟨2009151905851643142657217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678869207802190856876289 2009151905851643142657217)
            ·
              refine ⟨1506863929388732356992913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009151905851643142657217 1506863929388732356992913)
              ·
                refine ⟨1130147947041549267744685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506863929388732356992913 1130147947041549267744685)
                ·
                  refine ⟨423805480140580975404257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130147947041549267744685 423805480140580975404257)
                  ·
                    refine ⟨317854110105435731553193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423805480140580975404257 317854110105435731553193)
                    ·
                      refine ⟨238390582579076798664895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317854110105435731553193 238390582579076798664895)
                      ·
                        rfl

theorem cell23_464264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_464264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464264 prefixEnd_464264 := by exact prefixLift 464264
  have htrace : WordTrace (prefixWord ++ tailWord_464264) baseStart_464264 baseEnd_464264 := by
    simpa [prefixWord, tailWord_464264, baseEnd_464264] using wordTrace_append hprefix tailTrace_464264
  have hstable : (prefixWord ++ tailWord_464264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464264).length < 2 ^ (prefixWord ++ tailWord_464264).sum := by decide
  have hdescent : baseEnd_464264 < baseStart_464264 := by decide
  rcases family_descends (prefixWord ++ tailWord_464264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464267 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 3]
def baseStart_464267 : Nat := 118140960795 + 464267 * 2 ^ 59
def prefixEnd_464267 : Nat := 4983230072969 + 3 ^ 40 * 464267 * 2
def baseEnd_464267 : Nat := 238392123021040286927381

theorem tailTrace_464267 : CollatzResearch.WordTrace tailWord_464267 prefixEnd_464267 238392123021040286927381 := by
  unfold tailWord_464267
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933208609047424336071055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11288805739364949557380703 16933208609047424336071055)
  ·
    refine ⟨25399812913571136504106583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16933208609047424336071055 25399812913571136504106583)
    ·
      refine ⟨38099719370356704756159875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25399812913571136504106583 38099719370356704756159875)
      ·
        refine ⟨57149579055535057134239813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099719370356704756159875 57149579055535057134239813)
        ·
          refine ⟨10715546072912823212669965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57149579055535057134239813 10715546072912823212669965)
          ·
            refine ⟨4018329777342308704751237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10715546072912823212669965 4018329777342308704751237)
            ·
              refine ⟨753436833251682882140857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4018329777342308704751237 753436833251682882140857)
              ·
                refine ⟨565077624938762161605643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753436833251682882140857 565077624938762161605643)
                ·
                  refine ⟨847616437408143242408465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565077624938762161605643 847616437408143242408465)
                  ·
                    refine ⟨635712328056107431806349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 847616437408143242408465 635712328056107431806349)
                    ·
                      refine ⟨238392123021040286927381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635712328056107431806349 238392123021040286927381)
                      ·
                        rfl

theorem cell23_464267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 3].length) (baseStart_464267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464267 prefixEnd_464267 := by exact prefixLift 464267
  have htrace : WordTrace (prefixWord ++ tailWord_464267) baseStart_464267 baseEnd_464267 := by
    simpa [prefixWord, tailWord_464267, baseEnd_464267] using wordTrace_append hprefix tailTrace_464267
  have hstable : (prefixWord ++ tailWord_464267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464267).length < 2 ^ (prefixWord ++ tailWord_464267).sum := by decide
  have hdescent : baseEnd_464267 < baseStart_464267 := by decide
  rcases family_descends (prefixWord ++ tailWord_464267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464281 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 1, 2, 2]
def baseStart_464281 : Nat := 118140960795 + 464281 * 2 ^ 59
def prefixEnd_464281 : Nat := 4983230072969 + 3 ^ 40 * 464281 * 2
def baseEnd_464281 : Nat := 238399311750203232152317

theorem tailTrace_464281 : CollatzResearch.WordTrace tailWord_464281 prefixEnd_464281 238399311750203232152317 := by
  unfold tailWord_464281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933719230996704727080697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11289146153997803151387131 16933719230996704727080697)
  ·
    refine ⟨12700289423247528545310523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16933719230996704727080697 12700289423247528545310523)
    ·
      refine ⟨19050434134871292817965785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700289423247528545310523 19050434134871292817965785)
      ·
        refine ⟨14287825601153469613474339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19050434134871292817965785 14287825601153469613474339)
        ·
          refine ⟨21431738401730204420211509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287825601153469613474339 21431738401730204420211509)
          ·
            refine ⟨2009225475162206664394829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21431738401730204420211509 2009225475162206664394829)
            ·
              refine ⟨753459553185827499148061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2009225475162206664394829 753459553185827499148061)
              ·
                refine ⟨282547332444685312180523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753459553185827499148061 282547332444685312180523)
                ·
                  refine ⟨423820998667027968270785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282547332444685312180523 423820998667027968270785)
                  ·
                    refine ⟨317865749000270976203089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 423820998667027968270785 317865749000270976203089)
                    ·
                      refine ⟨238399311750203232152317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317865749000270976203089 238399311750203232152317)
                      ·
                        rfl

theorem cell23_464281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_464281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464281 prefixEnd_464281 := by exact prefixLift 464281
  have htrace : WordTrace (prefixWord ++ tailWord_464281) baseStart_464281 baseEnd_464281 := by
    simpa [prefixWord, tailWord_464281, baseEnd_464281] using wordTrace_append hprefix tailTrace_464281
  have hstable : (prefixWord ++ tailWord_464281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464281).length < 2 ^ (prefixWord ++ tailWord_464281).sum := by decide
  have hdescent : baseEnd_464281 < baseStart_464281 := by decide
  rcases family_descends (prefixWord ++ tailWord_464281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464284 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_464284 : Nat := 118140960795 + 464284 * 2 ^ 59
def prefixEnd_464284 : Nat := 4983230072969 + 3 ^ 40 * 464284 * 2
def baseEnd_464284 : Nat := 238400852192166720414803

theorem tailTrace_464284 : CollatzResearch.WordTrace tailWord_464284 prefixEnd_464284 238400852192166720414803 := by
  unfold tailWord_464284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466914324992918119719953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11289219099990557492959937 8466914324992918119719953)
  ·
    refine ⟨6350185743744688589789965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8466914324992918119719953 6350185743744688589789965)
    ·
      refine ⟨2381319653904258221171237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6350185743744688589789965 2381319653904258221171237)
      ·
        refine ⟨446497435107048416469607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2381319653904258221171237 446497435107048416469607)
        ·
          refine ⟨669746152660572624704411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446497435107048416469607 669746152660572624704411)
          ·
            refine ⟨1004619228990858937056617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669746152660572624704411 1004619228990858937056617)
            ·
              refine ⟨753464421743144202792463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004619228990858937056617 753464421743144202792463)
              ·
                refine ⟨1130196632614716304188695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753464421743144202792463 1130196632614716304188695)
                ·
                  refine ⟨1695294948922074456283043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130196632614716304188695 1695294948922074456283043)
                  ·
                    refine ⟨2542942423383111684424565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695294948922074456283043 2542942423383111684424565)
                    ·
                      refine ⟨238400852192166720414803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2542942423383111684424565 238400852192166720414803)
                      ·
                        rfl

theorem cell23_464284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_464284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464284 prefixEnd_464284 := by exact prefixLift 464284
  have htrace : WordTrace (prefixWord ++ tailWord_464284) baseStart_464284 baseEnd_464284 := by
    simpa [prefixWord, tailWord_464284, baseEnd_464284] using wordTrace_append hprefix tailTrace_464284
  have hstable : (prefixWord ++ tailWord_464284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464284).length < 2 ^ (prefixWord ++ tailWord_464284).sum := by decide
  have hdescent : baseEnd_464284 < baseStart_464284 := by decide
  rcases family_descends (prefixWord ++ tailWord_464284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464341 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_464341 : Nat := 118140960795 + 464341 * 2 ^ 59
def prefixEnd_464341 : Nat := 4983230072969 + 3 ^ 40 * 464341 * 2
def baseEnd_464341 : Nat := 238430120589472997402041

theorem tailTrace_464341 : CollatzResearch.WordTrace tailWord_464341 prefixEnd_464341 238430120589472997402041 := by
  unfold tailWord_464341
  simp only [CollatzResearch.WordTrace]
  refine ⟨16935907610779334974264877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11290605073852889982843251 16935907610779334974264877)
  ·
    refine ⟨6350965354042250615349329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16935907610779334974264877 6350965354042250615349329)
    ·
      refine ⟨4763224015531687961511997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6350965354042250615349329 4763224015531687961511997)
      ·
        refine ⟨1786209005824382985566999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4763224015531687961511997 1786209005824382985566999)
        ·
          refine ⟨2679313508736574478350499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786209005824382985566999 2679313508736574478350499)
          ·
            refine ⟨4018970263104861717525749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679313508736574478350499 4018970263104861717525749)
            ·
              refine ⟨376778462166080786018039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4018970263104861717525749 376778462166080786018039)
              ·
                refine ⟨565167693249121179027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376778462166080786018039 565167693249121179027059)
                ·
                  refine ⟨847751539873681768540589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565167693249121179027059 847751539873681768540589)
                  ·
                    refine ⟨317906827452630663202721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847751539873681768540589 317906827452630663202721)
                    ·
                      refine ⟨238430120589472997402041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 317906827452630663202721 238430120589472997402041)
                      ·
                        rfl

theorem cell23_464341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_464341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464341 prefixEnd_464341 := by exact prefixLift 464341
  have htrace : WordTrace (prefixWord ++ tailWord_464341) baseStart_464341 baseEnd_464341 := by
    simpa [prefixWord, tailWord_464341, baseEnd_464341] using wordTrace_append hprefix tailTrace_464341
  have hstable : (prefixWord ++ tailWord_464341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464341).length < 2 ^ (prefixWord ++ tailWord_464341).sum := by decide
  have hdescent : baseEnd_464341 < baseStart_464341 := by decide
  rcases family_descends (prefixWord ++ tailWord_464341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464357 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_464357 : Nat := 118140960795 + 464357 * 2 ^ 59
def prefixEnd_464357 : Nat := 4983230072969 + 3 ^ 40 * 464357 * 2
def baseEnd_464357 : Nat := 238438336279944934801967

theorem tailTrace_464357 : CollatzResearch.WordTrace tailWord_464357 prefixEnd_464357 238438336279944934801967 := by
  unfold tailWord_464357
  simp only [CollatzResearch.WordTrace]
  refine ⟨16936491178721369706847325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11290994119147579804564883 16936491178721369706847325)
  ·
    refine ⟨6351184192020513640067747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16936491178721369706847325 6351184192020513640067747)
    ·
      refine ⟨9526776288030770460101621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351184192020513640067747 9526776288030770460101621)
      ·
        refine ⟨893135277002884730634527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9526776288030770460101621 893135277002884730634527)
        ·
          refine ⟨1339702915504327095951791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893135277002884730634527 1339702915504327095951791)
          ·
            refine ⟨2009554373256490643927687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339702915504327095951791 2009554373256490643927687)
            ·
              refine ⟨3014331559884735965891531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009554373256490643927687 3014331559884735965891531)
              ·
                refine ⟨4521497339827103948837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014331559884735965891531 4521497339827103948837297)
                ·
                  refine ⟨3391123004870327961627973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521497339827103948837297 3391123004870327961627973)
                  ·
                    refine ⟨635835563413186492805245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391123004870327961627973 635835563413186492805245)
                    ·
                      refine ⟨238438336279944934801967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635835563413186492805245 238438336279944934801967)
                      ·
                        rfl

theorem cell23_464357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_464357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464357 prefixEnd_464357 := by exact prefixLift 464357
  have htrace : WordTrace (prefixWord ++ tailWord_464357) baseStart_464357 baseEnd_464357 := by
    simpa [prefixWord, tailWord_464357, baseEnd_464357] using wordTrace_append hprefix tailTrace_464357
  have hstable : (prefixWord ++ tailWord_464357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464357).length < 2 ^ (prefixWord ++ tailWord_464357).sum := by decide
  have hdescent : baseEnd_464357 < baseStart_464357 := by decide
  rcases family_descends (prefixWord ++ tailWord_464357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464360 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 7]
def baseStart_464360 : Nat := 118140960795 + 464360 * 2 ^ 59
def prefixEnd_464360 : Nat := 4983230072969 + 3 ^ 40 * 464360 * 2
def baseEnd_464360 : Nat := 26493319635767602562717

theorem tailTrace_464360 : CollatzResearch.WordTrace tailWord_464360 prefixEnd_464360 26493319635767602562717 := by
  unfold tailWord_464360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468300298855250609603267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11291067065140334146137689 8468300298855250609603267)
  ·
    refine ⟨12702450448282875914404901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8468300298855250609603267 12702450448282875914404901)
    ·
      refine ⟨2381709459053039233950919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12702450448282875914404901 2381709459053039233950919)
      ·
        refine ⟨3572564188579558850926379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381709459053039233950919 3572564188579558850926379)
        ·
          refine ⟨5358846282869338276389569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572564188579558850926379 5358846282869338276389569)
          ·
            refine ⟨4019134712152003707292177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358846282869338276389569 4019134712152003707292177)
            ·
              refine ⟨3014351034114002780469133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019134712152003707292177 3014351034114002780469133)
              ·
                refine ⟨1130381637792751042675925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3014351034114002780469133 1130381637792751042675925)
                ·
                  refine ⟨26493319635767602562717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1130381637792751042675925 26493319635767602562717)
                  ·
                    rfl

theorem cell23_464360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_464360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464360 prefixEnd_464360 := by exact prefixLift 464360
  have htrace : WordTrace (prefixWord ++ tailWord_464360) baseStart_464360 baseEnd_464360 := by
    simpa [prefixWord, tailWord_464360, baseEnd_464360] using wordTrace_append hprefix tailTrace_464360
  have hstable : (prefixWord ++ tailWord_464360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464360).length < 2 ^ (prefixWord ++ tailWord_464360).sum := by decide
  have hdescent : baseEnd_464360 < baseStart_464360 := by decide
  rcases family_descends (prefixWord ++ tailWord_464360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464394 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_464394 : Nat := 118140960795 + 464394 * 2 ^ 59
def prefixEnd_464394 : Nat := 4983230072969 + 3 ^ 40 * 464394 * 2
def baseEnd_464394 : Nat := 26495259451573476671033

theorem tailTrace_464394 : CollatzResearch.WordTrace tailWord_464394 prefixEnd_464394 26495259451573476671033 := by
  unfold tailWord_464394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234460169896831256486059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11291893786391550017296157 4234460169896831256486059)
  ·
    refine ⟨6351690254845246884729089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234460169896831256486059 6351690254845246884729089)
    ·
      refine ⟨4763767691133935163546817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351690254845246884729089 4763767691133935163546817)
      ·
        refine ⟨3572825768350451372660113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4763767691133935163546817 3572825768350451372660113)
        ·
          refine ⟨2679619326262838529495085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3572825768350451372660113 2679619326262838529495085)
          ·
            refine ⟨1004857247348564448560657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2679619326262838529495085 1004857247348564448560657)
            ·
              refine ⟨753642935511423336420493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004857247348564448560657 753642935511423336420493)
              ·
                refine ⟨282616100816783751157685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753642935511423336420493 282616100816783751157685)
                ·
                  refine ⟨26495259451573476671033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282616100816783751157685 26495259451573476671033)
                  ·
                    rfl

theorem cell23_464394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_464394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464394 prefixEnd_464394 := by exact prefixLift 464394
  have htrace : WordTrace (prefixWord ++ tailWord_464394) baseStart_464394 baseEnd_464394 := by
    simpa [prefixWord, tailWord_464394, baseEnd_464394] using wordTrace_append hprefix tailTrace_464394
  have hstable : (prefixWord ++ tailWord_464394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464394).length < 2 ^ (prefixWord ++ tailWord_464394).sum := by decide
  have hdescent : baseEnd_464394 < baseStart_464394 := by decide
  rcases family_descends (prefixWord ++ tailWord_464394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464447 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_464447 : Nat := 118140960795 + 464447 * 2 ^ 59
def prefixEnd_464447 : Nat := 4983230072969 + 3 ^ 40 * 464447 * 2
def baseEnd_464447 : Nat := 238484549538849582676553

theorem tailTrace_464447 : CollatzResearch.WordTrace tailWord_464447 prefixEnd_464447 238484549538849582676553 := by
  unfold tailWord_464447
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939773748395315077623595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11293182498930210051749063 16939773748395315077623595)
  ·
    refine ⟨25409660622592972616435393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16939773748395315077623595 25409660622592972616435393)
    ·
      refine ⟨19057245466944729462326545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25409660622592972616435393 19057245466944729462326545)
      ·
        refine ⟨14292934100208547096744909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19057245466944729462326545 14292934100208547096744909)
        ·
          refine ⟨5359850287578205161279341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14292934100208547096744909 5359850287578205161279341)
          ·
            refine ⟨2009943857841826935479753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5359850287578205161279341 2009943857841826935479753)
            ·
              refine ⟨1507457893381370201609815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009943857841826935479753 1507457893381370201609815)
              ·
                refine ⟨2261186840072055302414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507457893381370201609815 2261186840072055302414723)
                ·
                  refine ⟨3391780260108082953622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261186840072055302414723 3391780260108082953622085)
                  ·
                    refine ⟨635958798770265553804141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391780260108082953622085 635958798770265553804141)
                    ·
                      refine ⟨238484549538849582676553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 635958798770265553804141 238484549538849582676553)
                      ·
                        rfl

theorem cell23_464447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_464447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464447 prefixEnd_464447 := by exact prefixLift 464447
  have htrace : WordTrace (prefixWord ++ tailWord_464447) baseStart_464447 baseEnd_464447 := by
    simpa [prefixWord, tailWord_464447, baseEnd_464447] using wordTrace_append hprefix tailTrace_464447
  have hstable : (prefixWord ++ tailWord_464447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464447).length < 2 ^ (prefixWord ++ tailWord_464447).sum := by decide
  have hdescent : baseEnd_464447 < baseStart_464447 := by decide
  rcases family_descends (prefixWord ++ tailWord_464447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464461 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_464461 : Nat := 118140960795 + 464461 * 2 ^ 59
def prefixEnd_464461 : Nat := 4983230072969 + 3 ^ 40 * 464461 * 2
def baseEnd_464461 : Nat := 238491738268012527901489

theorem tailTrace_464461 : CollatzResearch.WordTrace tailWord_464461 prefixEnd_464461 238491738268012527901489 := by
  unfold tailWord_464461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940284370344595468633237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11293522913563063645755491 16940284370344595468633237)
  ·
    refine ⟨794075829859902912592183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16940284370344595468633237 794075829859902912592183)
    ·
      refine ⟨1191113744789854368888275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794075829859902912592183 1191113744789854368888275)
      ·
        refine ⟨1786670617184781553332413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191113744789854368888275 1786670617184781553332413)
        ·
          refine ⟨670001481444293082499655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1786670617184781553332413 670001481444293082499655)
          ·
            refine ⟨1005002222166439623749483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670001481444293082499655 1005002222166439623749483)
            ·
              refine ⟨1507503333249659435624225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005002222166439623749483 1507503333249659435624225)
              ·
                refine ⟨1130627499937244576718169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507503333249659435624225 1130627499937244576718169)
                ·
                  refine ⟨847970624952933432538627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1130627499937244576718169 847970624952933432538627)
                  ·
                    refine ⟨1271955937429400148807941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847970624952933432538627 1271955937429400148807941)
                    ·
                      refine ⟨238491738268012527901489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1271955937429400148807941 238491738268012527901489)
                      ·
                        rfl

theorem cell23_464461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_464461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464461 prefixEnd_464461 := by exact prefixLift 464461
  have htrace : WordTrace (prefixWord ++ tailWord_464461) baseStart_464461 baseEnd_464461 := by
    simpa [prefixWord, tailWord_464461, baseEnd_464461] using wordTrace_append hprefix tailTrace_464461
  have hstable : (prefixWord ++ tailWord_464461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464461).length < 2 ^ (prefixWord ++ tailWord_464461).sum := by decide
  have hdescent : baseEnd_464461 < baseStart_464461 := by decide
  rcases family_descends (prefixWord ++ tailWord_464461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464480 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_464480 : Nat := 118140960795 + 464480 * 2 ^ 59
def prefixEnd_464480 : Nat := 4983230072969 + 3 ^ 40 * 464480 * 2
def baseEnd_464480 : Nat := 79500498133482651187967

theorem tailTrace_464480 : CollatzResearch.WordTrace tailWord_464480 prefixEnd_464480 79500498133482651187967 := by
  unfold tailWord_464480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470488678637880856787447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11293984904850507809049929 8470488678637880856787447)
  ·
    refine ⟨12705733017956821285181171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8470488678637880856787447 12705733017956821285181171)
    ·
      refine ⟨19058599526935231927771757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705733017956821285181171 19058599526935231927771757)
      ·
        refine ⟨7146974822600711972914409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19058599526935231927771757 7146974822600711972914409)
        ·
          refine ⟨5360231116950533979685807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7146974822600711972914409 5360231116950533979685807)
          ·
            refine ⟨8040346675425800969528711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360231116950533979685807 8040346675425800969528711)
            ·
              refine ⟨12060520013138701454293067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8040346675425800969528711 12060520013138701454293067)
              ·
                refine ⟨18090780019708052181439601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12060520013138701454293067 18090780019708052181439601)
                ·
                  refine ⟨13568085014781039136079701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18090780019708052181439601 13568085014781039136079701)
                  ·
                    refine ⟨79500498133482651187967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13568085014781039136079701 79500498133482651187967)
                    ·
                      rfl

theorem cell23_464480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_464480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464480 prefixEnd_464480 := by exact prefixLift 464480
  have htrace : WordTrace (prefixWord ++ tailWord_464480) baseStart_464480 baseEnd_464480 := by
    simpa [prefixWord, tailWord_464480, baseEnd_464480] using wordTrace_append hprefix tailTrace_464480
  have hstable : (prefixWord ++ tailWord_464480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464480).length < 2 ^ (prefixWord ++ tailWord_464480).sum := by decide
  have hdescent : baseEnd_464480 < baseStart_464480 := by decide
  rcases family_descends (prefixWord ++ tailWord_464480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464484 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 6]
def baseStart_464484 : Nat := 118140960795 + 464484 * 2 ^ 59
def prefixEnd_464484 : Nat := 4983230072969 + 3 ^ 40 * 464484 * 2
def baseEnd_464484 : Nat := 26500394258118437545987

theorem tailTrace_464484 : CollatzResearch.WordTrace tailWord_464484 prefixEnd_464484 26500394258118437545987 := by
  unfold tailWord_464484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470561624630635198360253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11294082166174180264480337 8470561624630635198360253)
  ·
    refine ⟨3176460609236488199385095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8470561624630635198360253 3176460609236488199385095)
    ·
      refine ⟨4764690913854732299077643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176460609236488199385095 4764690913854732299077643)
      ·
        refine ⟨7147036370782098448616465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4764690913854732299077643 7147036370782098448616465)
        ·
          refine ⟨5360277278086573836462349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7147036370782098448616465 5360277278086573836462349)
          ·
            refine ⟨2010103979282465188673381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5360277278086573836462349 2010103979282465188673381)
            ·
              refine ⟨376894496115462222876259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2010103979282465188673381 376894496115462222876259)
              ·
                refine ⟨565341744173193334314389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376894496115462222876259 565341744173193334314389)
                ·
                  refine ⟨26500394258118437545987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 565341744173193334314389 26500394258118437545987)
                  ·
                    rfl

theorem cell23_464484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_464484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464484 prefixEnd_464484 := by exact prefixLift 464484
  have htrace : WordTrace (prefixWord ++ tailWord_464484) baseStart_464484 baseEnd_464484 := by
    simpa [prefixWord, tailWord_464484, baseEnd_464484] using wordTrace_append hprefix tailTrace_464484
  have hstable : (prefixWord ++ tailWord_464484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464484).length < 2 ^ (prefixWord ++ tailWord_464484).sum := by decide
  have hdescent : baseEnd_464484 < baseStart_464484 := by decide
  rcases family_descends (prefixWord ++ tailWord_464484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464544 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_464544 : Nat := 118140960795 + 464544 * 2 ^ 59
def prefixEnd_464544 : Nat := 4983230072969 + 3 ^ 40 * 464544 * 2
def baseEnd_464544 : Nat := 79511452387445234387869

theorem tailTrace_464544 : CollatzResearch.WordTrace tailWord_464544 prefixEnd_464544 79511452387445234387869 := by
  unfold tailWord_464544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471655814521950321952343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11295541086029267095936457 8471655814521950321952343)
  ·
    refine ⟨12707483721782925482928515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471655814521950321952343 12707483721782925482928515)
    ·
      refine ⟨19061225582674388224392773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707483721782925482928515 19061225582674388224392773)
      ·
        refine ⟨3573979796751447792073645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19061225582674388224392773 3573979796751447792073645)
        ·
          refine ⟨1340242423781792922027617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3573979796751447792073645 1340242423781792922027617)
          ·
            refine ⟨1005181817836344691520713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340242423781792922027617 1005181817836344691520713)
            ·
              refine ⟨753886363377258518640535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005181817836344691520713 753886363377258518640535)
              ·
                refine ⟨1130829545065887777960803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753886363377258518640535 1130829545065887777960803)
                ·
                  refine ⟨1696244317598831666941205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130829545065887777960803 1696244317598831666941205)
                  ·
                    refine ⟨79511452387445234387869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1696244317598831666941205 79511452387445234387869)
                    ·
                      rfl

theorem cell23_464544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_464544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464544 prefixEnd_464544 := by exact prefixLift 464544
  have htrace : WordTrace (prefixWord ++ tailWord_464544) baseStart_464544 baseEnd_464544 := by
    simpa [prefixWord, tailWord_464544, baseEnd_464544] using wordTrace_append hprefix tailTrace_464544
  have hstable : (prefixWord ++ tailWord_464544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464544).length < 2 ^ (prefixWord ++ tailWord_464544).sum := by decide
  have hdescent : baseEnd_464544 < baseStart_464544 := by decide
  rcases family_descends (prefixWord ++ tailWord_464544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464565 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_464565 : Nat := 118140960795 + 464565 * 2 ^ 59
def prefixEnd_464565 : Nat := 4983230072969 + 3 ^ 40 * 464565 * 2
def baseEnd_464565 : Nat := 79515046752026707000337

theorem tailTrace_464565 : CollatzResearch.WordTrace tailWord_464565 prefixEnd_464565 79515046752026707000337 := by
  unfold tailWord_464565
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944077561967821230419149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11296051707978547486946099 16944077561967821230419149)
  ·
    refine ⟨6354029085737932961407181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16944077561967821230419149 6354029085737932961407181)
    ·
      refine ⟨2382760907151724860527693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354029085737932961407181 2382760907151724860527693)
      ·
        refine ⟨893535340181896822697885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2382760907151724860527693 893535340181896822697885)
        ·
          refine ⟨335075752568211308511707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 893535340181896822697885 335075752568211308511707)
          ·
            refine ⟨502613628852316962767561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335075752568211308511707 502613628852316962767561)
            ·
              refine ⟨376960221639237722075671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502613628852316962767561 376960221639237722075671)
              ·
                refine ⟨565440332458856583113507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376960221639237722075671 565440332458856583113507)
                ·
                  refine ⟨848160498688284874670261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565440332458856583113507 848160498688284874670261)
                  ·
                    refine ⟨79515046752026707000337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 848160498688284874670261 79515046752026707000337)
                    ·
                      rfl

theorem cell23_464565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_464565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464565 prefixEnd_464565 := by exact prefixLift 464565
  have htrace : WordTrace (prefixWord ++ tailWord_464565) baseStart_464565 baseEnd_464565 := by
    simpa [prefixWord, tailWord_464565, baseEnd_464565] using wordTrace_append hprefix tailTrace_464565
  have hstable : (prefixWord ++ tailWord_464565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464565).length < 2 ^ (prefixWord ++ tailWord_464565).sum := by decide
  have hdescent : baseEnd_464565 < baseStart_464565 := by decide
  rcases family_descends (prefixWord ++ tailWord_464565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464598 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_464598 : Nat := 118140960795 + 464598 * 2 ^ 59
def prefixEnd_464598 : Nat := 4983230072969 + 3 ^ 40 * 464598 * 2
def baseEnd_464598 : Nat := 238562085117678491888359

theorem tailTrace_464598 : CollatzResearch.WordTrace tailWord_464598 prefixEnd_464598 238562085117678491888359 := by
  unfold tailWord_464598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059080073178016741648153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11296854113898845244246965 1059080073178016741648153)
  ·
    refine ⟨794310054883512556236115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1059080073178016741648153 794310054883512556236115)
    ·
      refine ⟨1191465082325268834354173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794310054883512556236115 1191465082325268834354173)
      ·
        refine ⟨446799405871975812882815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1191465082325268834354173 446799405871975812882815)
        ·
          refine ⟨670199108807963719324223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446799405871975812882815 670199108807963719324223)
          ·
            refine ⟨1005298663211945578986335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670199108807963719324223 1005298663211945578986335)
            ·
              refine ⟨1507947994817918368479503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005298663211945578986335 1507947994817918368479503)
              ·
                refine ⟨2261921992226877552719255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507947994817918368479503 2261921992226877552719255)
                ·
                  refine ⟨3392882988340316329078883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261921992226877552719255 3392882988340316329078883)
                  ·
                    refine ⟨5089324482510474493618325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392882988340316329078883 5089324482510474493618325)
                    ·
                      refine ⟨238562085117678491888359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5089324482510474493618325 238562085117678491888359)
                      ·
                        rfl

theorem cell23_464598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_464598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464598 prefixEnd_464598 := by exact prefixLift 464598
  have htrace : WordTrace (prefixWord ++ tailWord_464598) baseStart_464598 baseEnd_464598 := by
    simpa [prefixWord, tailWord_464598, baseEnd_464598] using wordTrace_append hprefix tailTrace_464598
  have hstable : (prefixWord ++ tailWord_464598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464598).length < 2 ^ (prefixWord ++ tailWord_464598).sum := by decide
  have hdescent : baseEnd_464598 < baseStart_464598 := by decide
  rcases family_descends (prefixWord ++ tailWord_464598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464601 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_464601 : Nat := 118140960795 + 464601 * 2 ^ 59
def prefixEnd_464601 : Nat := 4983230072969 + 3 ^ 40 * 464601 * 2
def baseEnd_464601 : Nat := 238563625559641980150845

theorem tailTrace_464601 : CollatzResearch.WordTrace tailWord_464601 prefixEnd_464601 238563625559641980150845 := by
  unfold tailWord_464601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945390589837399378729657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11296927059891599585819771 16945390589837399378729657)
  ·
    refine ⟨12709042942378049534047243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16945390589837399378729657 12709042942378049534047243)
    ·
      refine ⟨19063564413567074301070865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709042942378049534047243 19063564413567074301070865)
      ·
        refine ⟨14297673310175305725803149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19063564413567074301070865 14297673310175305725803149)
        ·
          refine ⟨5361627491315739647176181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14297673310175305725803149 5361627491315739647176181)
          ·
            refine ⟨502652577310850591922767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5361627491315739647176181 502652577310850591922767)
            ·
              refine ⟨753978865966275887884151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502652577310850591922767 753978865966275887884151)
              ·
                refine ⟨1130968298949413831826227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753978865966275887884151 1130968298949413831826227)
                ·
                  refine ⟨1696452448424120747739341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1130968298949413831826227 1696452448424120747739341)
                  ·
                    refine ⟨636169668159045280402253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1696452448424120747739341 636169668159045280402253)
                    ·
                      refine ⟨238563625559641980150845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636169668159045280402253 238563625559641980150845)
                      ·
                        rfl

theorem cell23_464601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_464601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464601 prefixEnd_464601 := by exact prefixLift 464601
  have htrace : WordTrace (prefixWord ++ tailWord_464601) baseStart_464601 baseEnd_464601 := by
    simpa [prefixWord, tailWord_464601, baseEnd_464601] using wordTrace_append hprefix tailTrace_464601
  have hstable : (prefixWord ++ tailWord_464601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464601).length < 2 ^ (prefixWord ++ tailWord_464601).sum := by decide
  have hdescent : baseEnd_464601 < baseStart_464601 := by decide
  rcases family_descends (prefixWord ++ tailWord_464601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464605 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_464605 : Nat := 118140960795 + 464605 * 2 ^ 59
def prefixEnd_464605 : Nat := 4983230072969 + 3 ^ 40 * 464605 * 2
def baseEnd_464605 : Nat := 238565679482259964500827

theorem tailTrace_464605 : CollatzResearch.WordTrace tailWord_464605 prefixEnd_464605 238565679482259964500827 := by
  unfold tailWord_464605
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945536481822908061875269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11297024321215272041250179 16945536481822908061875269)
  ·
    refine ⟨3177288090341795261601613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16945536481822908061875269 3177288090341795261601613)
    ·
      refine ⟨1191483033878173223100605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3177288090341795261601613 1191483033878173223100605)
      ·
        refine ⟨446806137704314958662727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1191483033878173223100605 446806137704314958662727)
        ·
          refine ⟨670209206556472437994091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446806137704314958662727 670209206556472437994091)
          ·
            refine ⟨1005313809834708656991137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670209206556472437994091 1005313809834708656991137)
            ·
              refine ⟨753985357376031492743353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005313809834708656991137 753985357376031492743353)
              ·
                refine ⟨565489018032023619557515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753985357376031492743353 565489018032023619557515)
                ·
                  refine ⟨848233527048035429336273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565489018032023619557515 848233527048035429336273)
                  ·
                    refine ⟨636175145286026572002205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848233527048035429336273 636175145286026572002205)
                    ·
                      refine ⟨238565679482259964500827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636175145286026572002205 238565679482259964500827)
                      ·
                        rfl

theorem cell23_464605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_464605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464605 prefixEnd_464605 := by exact prefixLift 464605
  have htrace : WordTrace (prefixWord ++ tailWord_464605) baseStart_464605 baseEnd_464605 := by
    simpa [prefixWord, tailWord_464605, baseEnd_464605] using wordTrace_append hprefix tailTrace_464605
  have hstable : (prefixWord ++ tailWord_464605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464605).length < 2 ^ (prefixWord ++ tailWord_464605).sum := by decide
  have hdescent : baseEnd_464605 < baseStart_464605 := by decide
  rcases family_descends (prefixWord ++ tailWord_464605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464627 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_464627 : Nat := 118140960795 + 464627 * 2 ^ 59
def prefixEnd_464627 : Nat := 4983230072969 + 3 ^ 40 * 464627 * 2
def baseEnd_464627 : Nat := 238576976056658878425725

theorem tailTrace_464627 : CollatzResearch.WordTrace tailWord_464627 prefixEnd_464627 238576976056658878425725 := by
  unfold tailWord_464627
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946338887743205819176135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11297559258495470546117423 16946338887743205819176135)
  ·
    refine ⟨25419508331614808728764203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16946338887743205819176135 25419508331614808728764203)
    ·
      refine ⟨38129262497422213093146305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25419508331614808728764203 38129262497422213093146305)
      ·
        refine ⟨28596946873066659819859729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38129262497422213093146305 28596946873066659819859729)
        ·
          refine ⟨21447710154799994864894797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28596946873066659819859729 21447710154799994864894797)
          ·
            refine ⟨8042891308049998074335549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21447710154799994864894797 8042891308049998074335549)
            ·
              refine ⟨3016084240518749277875831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8042891308049998074335549 3016084240518749277875831)
              ·
                refine ⟨4524126360778123916813747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016084240518749277875831 4524126360778123916813747)
                ·
                  refine ⟨6786189541167185875220621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524126360778123916813747 6786189541167185875220621)
                  ·
                    refine ⟨2544821077937694703207733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6786189541167185875220621 2544821077937694703207733)
                    ·
                      refine ⟨238576976056658878425725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2544821077937694703207733 238576976056658878425725)
                      ·
                        rfl

theorem cell23_464627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_464627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464627 prefixEnd_464627 := by exact prefixLift 464627
  have htrace : WordTrace (prefixWord ++ tailWord_464627) baseStart_464627 baseEnd_464627 := by
    simpa [prefixWord, tailWord_464627, baseEnd_464627] using wordTrace_append hprefix tailTrace_464627
  have hstable : (prefixWord ++ tailWord_464627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464627).length < 2 ^ (prefixWord ++ tailWord_464627).sum := by decide
  have hdescent : baseEnd_464627 < baseStart_464627 := by decide
  rcases family_descends (prefixWord ++ tailWord_464627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464637 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_464637 : Nat := 118140960795 + 464637 * 2 ^ 59
def prefixEnd_464637 : Nat := 4983230072969 + 3 ^ 40 * 464637 * 2
def baseEnd_464637 : Nat := 238582110863203839300679

theorem tailTrace_464637 : CollatzResearch.WordTrace tailWord_464637 prefixEnd_464637 238582110863203839300679 := by
  unfold tailWord_464637
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946703617706977527040165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11297802411804651684693443 16946703617706977527040165)
  ·
    refine ⟨3177506928320058286320031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16946703617706977527040165 3177506928320058286320031)
    ·
      refine ⟨4766260392480087429480047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177506928320058286320031 4766260392480087429480047)
      ·
        refine ⟨7149390588720131144220071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766260392480087429480047 7149390588720131144220071)
        ·
          refine ⟨10724085883080196716330107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149390588720131144220071 10724085883080196716330107)
          ·
            refine ⟨16086128824620295074495161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724085883080196716330107 16086128824620295074495161)
            ·
              refine ⟨12064596618465221305871371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16086128824620295074495161 12064596618465221305871371)
              ·
                refine ⟨18096894927697831958807057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064596618465221305871371 18096894927697831958807057)
                ·
                  refine ⟨13572671195773373969105293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18096894927697831958807057 13572671195773373969105293)
                  ·
                    refine ⟨5089751698415015238414485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13572671195773373969105293 5089751698415015238414485)
                    ·
                      refine ⟨238582110863203839300679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5089751698415015238414485 238582110863203839300679)
                      ·
                        rfl

theorem cell23_464637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_464637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464637 prefixEnd_464637 := by exact prefixLift 464637
  have htrace : WordTrace (prefixWord ++ tailWord_464637) baseStart_464637 baseEnd_464637 := by
    simpa [prefixWord, tailWord_464637, baseEnd_464637] using wordTrace_append hprefix tailTrace_464637
  have hstable : (prefixWord ++ tailWord_464637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464637).length < 2 ^ (prefixWord ++ tailWord_464637).sum := by decide
  have hdescent : baseEnd_464637 < baseStart_464637 := by decide
  rcases family_descends (prefixWord ++ tailWord_464637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464654 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_464654 : Nat := 118140960795 + 464654 * 2 ^ 59
def prefixEnd_464654 : Nat := 4983230072969 + 3 ^ 40 * 464654 * 2
def baseEnd_464654 : Nat := 238590840034330272788101

theorem tailTrace_464654 : CollatzResearch.WordTrace tailWord_464654 prefixEnd_464654 238590840034330272788101 := by
  unfold tailWord_464654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118415457330673678801127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11298215772430259620272677 2118415457330673678801127)
  ·
    refine ⟨3177623185996010518201691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118415457330673678801127 3177623185996010518201691)
    ·
      refine ⟨4766434778994015777302537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177623185996010518201691 4766434778994015777302537)
      ·
        refine ⟨3574826084245511832976903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4766434778994015777302537 3574826084245511832976903)
        ·
          refine ⟨5362239126368267749465355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574826084245511832976903 5362239126368267749465355)
          ·
            refine ⟨8043358689552401624198033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362239126368267749465355 8043358689552401624198033)
            ·
              refine ⟨6032519017164301218148525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8043358689552401624198033 6032519017164301218148525)
              ·
                refine ⟨2262194631436612956805697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6032519017164301218148525 2262194631436612956805697)
                ·
                  refine ⟨1696645973577459717604273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2262194631436612956805697 1696645973577459717604273)
                  ·
                    refine ⟨1272484480183094788203205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1696645973577459717604273 1272484480183094788203205)
                    ·
                      refine ⟨238590840034330272788101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1272484480183094788203205 238590840034330272788101)
                      ·
                        rfl

theorem cell23_464654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_464654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464654 prefixEnd_464654 := by exact prefixLift 464654
  have htrace : WordTrace (prefixWord ++ tailWord_464654) baseStart_464654 baseEnd_464654 := by
    simpa [prefixWord, tailWord_464654, baseEnd_464654] using wordTrace_append hprefix tailTrace_464654
  have hstable : (prefixWord ++ tailWord_464654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464654).length < 2 ^ (prefixWord ++ tailWord_464654).sum := by decide
  have hdescent : baseEnd_464654 < baseStart_464654 := by decide
  rcases family_descends (prefixWord ++ tailWord_464654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464687 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_464687 : Nat := 118140960795 + 464687 * 2 ^ 59
def prefixEnd_464687 : Nat := 4983230072969 + 3 ^ 40 * 464687 * 2
def baseEnd_464687 : Nat := 238607784895928643675449

theorem tailTrace_464687 : CollatzResearch.WordTrace tailWord_464687 prefixEnd_464687 238607784895928643675449 := by
  unfold tailWord_464687
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948527267525836066360315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11299018178350557377573543 16948527267525836066360315)
  ·
    refine ⟨25422790901288754099540473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16948527267525836066360315 25422790901288754099540473)
    ·
      refine ⟨19067093175966565574655355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25422790901288754099540473 19067093175966565574655355)
      ·
        refine ⟨28600639763949848361983033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19067093175966565574655355 28600639763949848361983033)
        ·
          refine ⟨21450479822962386271487275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28600639763949848361983033 21450479822962386271487275)
          ·
            refine ⟨32175719734443579407230913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21450479822962386271487275 32175719734443579407230913)
            ·
              refine ⟨24131789800832684555423185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32175719734443579407230913 24131789800832684555423185)
              ·
                refine ⟨18098842350624513416567389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24131789800832684555423185 18098842350624513416567389)
                ·
                  refine ⟨6787065881484192531212771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18098842350624513416567389 6787065881484192531212771)
                  ·
                    refine ⟨10180598822226288796819157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6787065881484192531212771 10180598822226288796819157)
                    ·
                      refine ⟨238607784895928643675449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10180598822226288796819157 238607784895928643675449)
                      ·
                        rfl

theorem cell23_464687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_464687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464687 prefixEnd_464687 := by exact prefixLift 464687
  have htrace : WordTrace (prefixWord ++ tailWord_464687) baseStart_464687 baseEnd_464687 := by
    simpa [prefixWord, tailWord_464687, baseEnd_464687] using wordTrace_append hprefix tailTrace_464687
  have hstable : (prefixWord ++ tailWord_464687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464687).length < 2 ^ (prefixWord ++ tailWord_464687).sum := by decide
  have hdescent : baseEnd_464687 < baseStart_464687 := by decide
  rcases family_descends (prefixWord ++ tailWord_464687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464692 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_464692 : Nat := 118140960795 + 464692 * 2 ^ 59
def prefixEnd_464692 : Nat := 4983230072969 + 3 ^ 40 * 464692 * 2
def baseEnd_464692 : Nat := 238610352299201124112927

theorem tailTrace_464692 : CollatzResearch.WordTrace tailWord_464692 prefixEnd_464692 238610352299201124112927 := by
  unfold tailWord_464692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474354816253860960146165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11299139755005147946861553 8474354816253860960146165)
  ·
    refine ⟨794470764023799465013703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8474354816253860960146165 794470764023799465013703)
    ·
      refine ⟨1191706146035699197520555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794470764023799465013703 1191706146035699197520555)
      ·
        refine ⟨1787559219053548796280833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191706146035699197520555 1787559219053548796280833)
        ·
          refine ⟨1340669414290161597210625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787559219053548796280833 1340669414290161597210625)
          ·
            refine ⟨1005502060717621197907969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340669414290161597210625 1005502060717621197907969)
            ·
              refine ⟨754126545538215898430977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005502060717621197907969 754126545538215898430977)
              ·
                refine ⟨565594909153661923823233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754126545538215898430977 565594909153661923823233)
                ·
                  refine ⟨424196181865246442867425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565594909153661923823233 424196181865246442867425)
                  ·
                    refine ⟨318147136398934832150569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424196181865246442867425 318147136398934832150569)
                    ·
                      refine ⟨238610352299201124112927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318147136398934832150569 238610352299201124112927)
                      ·
                        rfl

theorem cell23_464692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_464692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464692 prefixEnd_464692 := by exact prefixLift 464692
  have htrace : WordTrace (prefixWord ++ tailWord_464692) baseStart_464692 baseEnd_464692 := by
    simpa [prefixWord, tailWord_464692, baseEnd_464692] using wordTrace_append hprefix tailTrace_464692
  have hstable : (prefixWord ++ tailWord_464692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464692).length < 2 ^ (prefixWord ++ tailWord_464692).sum := by decide
  have hdescent : baseEnd_464692 < baseStart_464692 := by decide
  rcases family_descends (prefixWord ++ tailWord_464692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464698 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_464698 : Nat := 118140960795 + 464698 * 2 ^ 59
def prefixEnd_464698 : Nat := 4983230072969 + 3 ^ 40 * 464698 * 2
def baseEnd_464698 : Nat := 26512603687014233404211

theorem tailTrace_464698 : CollatzResearch.WordTrace tailWord_464698 prefixEnd_464698 26512603687014233404211 := by
  unfold tailWord_464698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237232117621496236252687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11299285646990656630007165 4237232117621496236252687)
  ·
    refine ⟨6355848176432244354379031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237232117621496236252687 6355848176432244354379031)
    ·
      refine ⟨9533772264648366531568547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6355848176432244354379031 9533772264648366531568547)
      ·
        refine ⟨14300658396972549797352821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9533772264648366531568547 14300658396972549797352821)
        ·
          refine ⟨1340686724716176543501827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14300658396972549797352821 1340686724716176543501827)
          ·
            refine ⟨2011030087074264815252741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340686724716176543501827 2011030087074264815252741)
            ·
              refine ⟨377068141326424652859889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2011030087074264815252741 377068141326424652859889)
              ·
                refine ⟨282801105994818489644917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377068141326424652859889 282801105994818489644917)
                ·
                  refine ⟨26512603687014233404211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282801105994818489644917 26512603687014233404211)
                  ·
                    rfl

theorem cell23_464698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_464698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464698 prefixEnd_464698 := by exact prefixLift 464698
  have htrace : WordTrace (prefixWord ++ tailWord_464698) baseStart_464698 baseEnd_464698 := by
    simpa [prefixWord, tailWord_464698, baseEnd_464698] using wordTrace_append hprefix tailTrace_464698
  have hstable : (prefixWord ++ tailWord_464698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464698).length < 2 ^ (prefixWord ++ tailWord_464698).sum := by decide
  have hdescent : baseEnd_464698 < baseStart_464698 := by decide
  rcases family_descends (prefixWord ++ tailWord_464698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464714 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_464714 : Nat := 118140960795 + 464714 * 2 ^ 59
def prefixEnd_464714 : Nat := 4983230072969 + 3 ^ 40 * 464714 * 2
def baseEnd_464714 : Nat := 238621648873600038037825

theorem tailTrace_464714 : CollatzResearch.WordTrace tailWord_464714 prefixEnd_464714 238621648873600038037825 := by
  unfold tailWord_464714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237378009607004919398299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11299674692285346451728797 4237378009607004919398299)
  ·
    refine ⟨6356067014410507379097449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237378009607004919398299 6356067014410507379097449)
    ·
      refine ⟨4767050260807880534323087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6356067014410507379097449 4767050260807880534323087)
      ·
        refine ⟨7150575391211820801484631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767050260807880534323087 7150575391211820801484631)
        ·
          refine ⟨10725863086817731202226947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150575391211820801484631 10725863086817731202226947)
          ·
            refine ⟨16088794630226596803340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725863086817731202226947 16088794630226596803340421)
            ·
              refine ⟨3016648993167486900626329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16088794630226596803340421 3016648993167486900626329)
              ·
                refine ⟨2262486744875615175469747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016648993167486900626329 2262486744875615175469747)
                ·
                  refine ⟨3393730117313422763204621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262486744875615175469747 3393730117313422763204621)
                  ·
                    refine ⟨1272648793992533536201733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3393730117313422763204621 1272648793992533536201733)
                    ·
                      refine ⟨238621648873600038037825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1272648793992533536201733 238621648873600038037825)
                      ·
                        rfl

theorem cell23_464714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_464714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464714 prefixEnd_464714 := by exact prefixLift 464714
  have htrace : WordTrace (prefixWord ++ tailWord_464714) baseStart_464714 baseEnd_464714 := by
    simpa [prefixWord, tailWord_464714, baseEnd_464714] using wordTrace_append hprefix tailTrace_464714
  have hstable : (prefixWord ++ tailWord_464714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464714).length < 2 ^ (prefixWord ++ tailWord_464714).sum := by decide
  have hdescent : baseEnd_464714 < baseStart_464714 := by decide
  rcases family_descends (prefixWord ++ tailWord_464714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464744 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_464744 : Nat := 118140960795 + 464744 * 2 ^ 59
def prefixEnd_464744 : Nat := 4983230072969 + 3 ^ 40 * 464744 * 2
def baseEnd_464744 : Nat := 238637053293234920662687

theorem tailTrace_464744 : CollatzResearch.WordTrace tailWord_464744 prefixEnd_464744 238637053293234920662687 := by
  unfold tailWord_464744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475303114159667400592643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11300404152212889867456857 8475303114159667400592643)
  ·
    refine ⟨12712954671239501100888965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8475303114159667400592643 12712954671239501100888965)
    ·
      refine ⟨2383679000857406456416681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12712954671239501100888965 2383679000857406456416681)
      ·
        refine ⟨1787759250643054842312511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383679000857406456416681 1787759250643054842312511)
        ·
          refine ⟨2681638875964582263468767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787759250643054842312511 2681638875964582263468767)
          ·
            refine ⟨4022458313946873395203151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681638875964582263468767 4022458313946873395203151)
            ·
              refine ⟨6033687470920310092804727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022458313946873395203151 6033687470920310092804727)
              ·
                refine ⟨9050531206380465139207091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033687470920310092804727 9050531206380465139207091)
                ·
                  refine ⟨13575796809570697708810637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050531206380465139207091 13575796809570697708810637)
                  ·
                    refine ⟨5090923803589011640803989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13575796809570697708810637 5090923803589011640803989)
                    ·
                      refine ⟨238637053293234920662687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5090923803589011640803989 238637053293234920662687)
                      ·
                        rfl

theorem cell23_464744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_464744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464744 prefixEnd_464744 := by exact prefixLift 464744
  have htrace : WordTrace (prefixWord ++ tailWord_464744) baseStart_464744 baseEnd_464744 := by
    simpa [prefixWord, tailWord_464744, baseEnd_464744] using wordTrace_append hprefix tailTrace_464744
  have hstable : (prefixWord ++ tailWord_464744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464744).length < 2 ^ (prefixWord ++ tailWord_464744).sum := by decide
  have hdescent : baseEnd_464744 < baseStart_464744 := by decide
  rcases family_descends (prefixWord ++ tailWord_464744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464841 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_464841 : Nat := 118140960795 + 464841 * 2 ^ 59
def prefixEnd_464841 : Nat := 4983230072969 + 3 ^ 40 * 464841 * 2
def baseEnd_464841 : Nat := 238686860916721041149741

theorem tailTrace_464841 : CollatzResearch.WordTrace tailWord_464841 prefixEnd_464841 238686860916721041149741 := by
  unfold tailWord_464841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954144108967920367466377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11302762739311946911644251 16954144108967920367466377)
  ·
    refine ⟨12715608081725940275599783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16954144108967920367466377 12715608081725940275599783)
    ·
      refine ⟨19073412122588910413399675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12715608081725940275599783 19073412122588910413399675)
      ·
        refine ⟨28610118183883365620099513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19073412122588910413399675 28610118183883365620099513)
        ·
          refine ⟨21457588637912524215074635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28610118183883365620099513 21457588637912524215074635)
          ·
            refine ⟨32186382956868786322611953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457588637912524215074635 32186382956868786322611953)
            ·
              refine ⟨24139787217651589741958965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32186382956868786322611953 24139787217651589741958965)
              ·
                refine ⟨2263105051654836538308653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24139787217651589741958965 2263105051654836538308653)
                ·
                  refine ⟨848664394370563701865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2263105051654836538308653 848664394370563701865745)
                  ·
                    refine ⟨636498295777922776399309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 848664394370563701865745 636498295777922776399309)
                    ·
                      refine ⟨238686860916721041149741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636498295777922776399309 238686860916721041149741)
                      ·
                        rfl

theorem cell23_464841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_464841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464841 prefixEnd_464841 := by exact prefixLift 464841
  have htrace : WordTrace (prefixWord ++ tailWord_464841) baseStart_464841 baseEnd_464841 := by
    simpa [prefixWord, tailWord_464841, baseEnd_464841] using wordTrace_append hprefix tailTrace_464841
  have hstable : (prefixWord ++ tailWord_464841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464841).length < 2 ^ (prefixWord ++ tailWord_464841).sum := by decide
  have hdescent : baseEnd_464841 < baseStart_464841 := by decide
  rcases family_descends (prefixWord ++ tailWord_464841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464861 : List Nat := [1, 4, 3, 1, 3, 11]
def baseStart_464861 : Nat := 118140960795 + 464861 * 2 ^ 59
def prefixEnd_464861 : Nat := 4983230072969 + 3 ^ 40 * 464861 * 2
def baseEnd_464861 : Nat := 982292718229674744443

theorem tailTrace_464861 : CollatzResearch.WordTrace tailWord_464861 prefixEnd_464861 982292718229674744443 := by
  unfold tailWord_464861
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954873568895463783194437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11303249045930309188796291 16954873568895463783194437)
  ·
    refine ⟨3179038794167899459348957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16954873568895463783194437 3179038794167899459348957)
    ·
      refine ⟨1192139547812962297255859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3179038794167899459348957 1192139547812962297255859)
      ·
        refine ⟨1788209321719443445883789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192139547812962297255859 1788209321719443445883789)
        ·
          refine ⟨670578495644791292206421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788209321719443445883789 670578495644791292206421)
          ·
            refine ⟨982292718229674744443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 670578495644791292206421 982292718229674744443)
            ·
              rfl

theorem cell23_464861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 11].length) (baseStart_464861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464861 prefixEnd_464861 := by exact prefixLift 464861
  have htrace : WordTrace (prefixWord ++ tailWord_464861) baseStart_464861 baseEnd_464861 := by
    simpa [prefixWord, tailWord_464861, baseEnd_464861] using wordTrace_append hprefix tailTrace_464861
  have hstable : (prefixWord ++ tailWord_464861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464861).length < 2 ^ (prefixWord ++ tailWord_464861).sum := by decide
  have hdescent : baseEnd_464861 < baseStart_464861 := by decide
  rcases family_descends (prefixWord ++ tailWord_464861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464878 : List Nat := [4, 1, 2, 1, 3, 3, 1, 8]
def baseStart_464878 : Nat := 118140960795 + 464878 * 2 ^ 59
def prefixEnd_464878 : Nat := 4983230072969 + 3 ^ 40 * 464878 * 2
def baseEnd_464878 : Nat := 8840957766701385051373

theorem tailTrace_464878 : CollatzResearch.WordTrace tailWord_464878 prefixEnd_464878 8840957766701385051373 := by
  unfold tailWord_464878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119436701229234460820411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11303662406555917124375525 2119436701229234460820411)
  ·
    refine ⟨3179155051843851691230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119436701229234460820411 3179155051843851691230617)
    ·
      refine ⟨2384366288882888768422963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179155051843851691230617 2384366288882888768422963)
      ·
        refine ⟨3576549433324333152634445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384366288882888768422963 3576549433324333152634445)
        ·
          refine ⟨1341206037496624932237917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3576549433324333152634445 1341206037496624932237917)
          ·
            refine ⟨502952264061234349589219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1341206037496624932237917 502952264061234349589219)
            ·
              refine ⟨754428396091851524383829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502952264061234349589219 754428396091851524383829)
              ·
                refine ⟨8840957766701385051373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 754428396091851524383829 8840957766701385051373)
                ·
                  rfl

theorem cell23_464878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_464878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464878 prefixEnd_464878 := by exact prefixLift 464878
  have htrace : WordTrace (prefixWord ++ tailWord_464878) baseStart_464878 baseEnd_464878 := by
    simpa [prefixWord, tailWord_464878, baseEnd_464878] using wordTrace_append hprefix tailTrace_464878
  have hstable : (prefixWord ++ tailWord_464878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464878).length < 2 ^ (prefixWord ++ tailWord_464878).sum := by decide
  have hdescent : baseEnd_464878 < baseStart_464878 := by decide
  rcases family_descends (prefixWord ++ tailWord_464878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464916 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_464916 : Nat := 118140960795 + 464916 * 2 ^ 59
def prefixEnd_464916 : Nat := 4983230072969 + 3 ^ 40 * 464916 * 2
def baseEnd_464916 : Nat := 79575123988602749237299

theorem tailTrace_464916 : CollatzResearch.WordTrace tailWord_464916 prefixEnd_464916 79575123988602749237299 := by
  unfold tailWord_464916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478439791848104088223301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11304586389130805450964401 8478439791848104088223301)
  ·
    refine ⟨1589707460971519516541869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8478439791848104088223301 1589707460971519516541869)
    ·
      refine ⟨596140297864319818703201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1589707460971519516541869 596140297864319818703201)
      ·
        refine ⟨447105223398239864027401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596140297864319818703201 447105223398239864027401)
        ·
          refine ⟨335328917548679898020551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447105223398239864027401 335328917548679898020551)
          ·
            refine ⟨502993376323019847030827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335328917548679898020551 502993376323019847030827)
            ·
              refine ⟨754490064484529770546241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502993376323019847030827 754490064484529770546241)
              ·
                refine ⟨565867548363397327909681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754490064484529770546241 565867548363397327909681)
                ·
                  refine ⟨424400661272547995932261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565867548363397327909681 424400661272547995932261)
                  ·
                    refine ⟨79575123988602749237299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424400661272547995932261 79575123988602749237299)
                    ·
                      rfl

theorem cell23_464916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_464916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464916 prefixEnd_464916 := by exact prefixLift 464916
  have htrace : WordTrace (prefixWord ++ tailWord_464916) baseStart_464916 baseEnd_464916 := by
    simpa [prefixWord, tailWord_464916, baseEnd_464916] using wordTrace_append hprefix tailTrace_464916
  have hstable : (prefixWord ++ tailWord_464916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464916).length < 2 ^ (prefixWord ++ tailWord_464916).sum := by decide
  have hdescent : baseEnd_464916 < baseStart_464916 := by decide
  rcases family_descends (prefixWord ++ tailWord_464916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464922 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_464922 : Nat := 118140960795 + 464922 * 2 ^ 59
def prefixEnd_464922 : Nat := 4983230072969 + 3 ^ 40 * 464922 * 2
def baseEnd_464922 : Nat := 238728452849735224236869

theorem tailTrace_464922 : CollatzResearch.WordTrace tailWord_464922 prefixEnd_464922 238728452849735224236869 := by
  unfold tailWord_464922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239274605418617800291255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11304732281116314134110013 4239274605418617800291255)
  ·
    refine ⟨6358911908127926700436883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239274605418617800291255 6358911908127926700436883)
    ·
      refine ⟨9538367862191890050655325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358911908127926700436883 9538367862191890050655325)
      ·
        refine ⟨3576887948321958768995747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9538367862191890050655325 3576887948321958768995747)
        ·
          refine ⟨5365331922482938153493621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576887948321958768995747 5365331922482938153493621)
          ·
            refine ⟨502999867732775451890027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5365331922482938153493621 502999867732775451890027)
            ·
              refine ⟨754499801599163177835041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502999867732775451890027 754499801599163177835041)
              ·
                refine ⟨565874851199372383376281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754499801599163177835041 565874851199372383376281)
                ·
                  refine ⟨424406138399529287532211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565874851199372383376281 424406138399529287532211)
                  ·
                    refine ⟨636609207599293931298317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424406138399529287532211 636609207599293931298317)
                    ·
                      refine ⟨238728452849735224236869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636609207599293931298317 238728452849735224236869)
                      ·
                        rfl

theorem cell23_464922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_464922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464922 prefixEnd_464922 := by exact prefixLift 464922
  have htrace : WordTrace (prefixWord ++ tailWord_464922) baseStart_464922 baseEnd_464922 := by
    simpa [prefixWord, tailWord_464922, baseEnd_464922] using wordTrace_append hprefix tailTrace_464922
  have hstable : (prefixWord ++ tailWord_464922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464922).length < 2 ^ (prefixWord ++ tailWord_464922).sum := by decide
  have hdescent : baseEnd_464922 < baseStart_464922 := by decide
  rcases family_descends (prefixWord ++ tailWord_464922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464938 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_464938 : Nat := 118140960795 + 464938 * 2 ^ 59
def prefixEnd_464938 : Nat := 4983230072969 + 3 ^ 40 * 464938 * 2
def baseEnd_464938 : Nat := 79578889513402387212265

theorem tailTrace_464938 : CollatzResearch.WordTrace tailWord_464938 prefixEnd_464938 79578889513402387212265 := by
  unfold tailWord_464938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239420497404126483436867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11305121326411003955831645 4239420497404126483436867)
  ·
    refine ⟨6359130746106189725155301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239420497404126483436867 6359130746106189725155301)
    ·
      refine ⟨1192337014894910573466619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6359130746106189725155301 1192337014894910573466619)
      ·
        refine ⟨1788505522342365860199929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192337014894910573466619 1788505522342365860199929)
        ·
          refine ⟨1341379141756774395149947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788505522342365860199929 1341379141756774395149947)
          ·
            refine ⟨2012068712635161592724921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341379141756774395149947 2012068712635161592724921)
            ·
              refine ⟨1509051534476371194543691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012068712635161592724921 1509051534476371194543691)
              ·
                refine ⟨2263577301714556791815537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509051534476371194543691 2263577301714556791815537)
                ·
                  refine ⟨1697682976285917593861653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2263577301714556791815537 1697682976285917593861653)
                  ·
                    refine ⟨79578889513402387212265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1697682976285917593861653 79578889513402387212265)
                    ·
                      rfl

theorem cell23_464938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_464938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464938 prefixEnd_464938 := by exact prefixLift 464938
  have htrace : WordTrace (prefixWord ++ tailWord_464938) baseStart_464938 baseEnd_464938 := by
    simpa [prefixWord, tailWord_464938, baseEnd_464938] using wordTrace_append hprefix tailTrace_464938
  have hstable : (prefixWord ++ tailWord_464938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464938).length < 2 ^ (prefixWord ++ tailWord_464938).sum := by decide
  have hdescent : baseEnd_464938 < baseStart_464938 := by decide
  rcases family_descends (prefixWord ++ tailWord_464938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464945 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_464945 : Nat := 118140960795 + 464945 * 2 ^ 59
def prefixEnd_464945 : Nat := 4983230072969 + 3 ^ 40 * 464945 * 2
def baseEnd_464945 : Nat := 238740262904788634249263

theorem tailTrace_464945 : CollatzResearch.WordTrace tailWord_464945 prefixEnd_464945 238740262904788634249263 := by
  unfold tailWord_464945
  simp only [CollatzResearch.WordTrace]
  refine ⟨16957937300591146129252289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11305291533727430752834859 16957937300591146129252289)
  ·
    refine ⟨12718452975443359596939217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16957937300591146129252289 12718452975443359596939217)
    ·
      refine ⟨9538839731582519697704413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12718452975443359596939217 9538839731582519697704413)
      ·
        refine ⟨3577064899343444886639155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9538839731582519697704413 3577064899343444886639155)
        ·
          refine ⟨5365597349015167329958733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577064899343444886639155 5365597349015167329958733)
          ·
            refine ⟨2012099005880687748734525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5365597349015167329958733 2012099005880687748734525)
            ·
              refine ⟨754537127205257905775447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2012099005880687748734525 754537127205257905775447)
              ·
                refine ⟨1131805690807886858663171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754537127205257905775447 1131805690807886858663171)
                ·
                  refine ⟨1697708536211830287994757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1131805690807886858663171 1697708536211830287994757)
                  ·
                    refine ⟨318320350539718178999017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1697708536211830287994757 318320350539718178999017)
                    ·
                      refine ⟨238740262904788634249263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318320350539718178999017 238740262904788634249263)
                      ·
                        rfl

theorem cell23_464945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_464945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464945 prefixEnd_464945 := by exact prefixLift 464945
  have htrace : WordTrace (prefixWord ++ tailWord_464945) baseStart_464945 baseEnd_464945 := by
    simpa [prefixWord, tailWord_464945, baseEnd_464945] using wordTrace_append hprefix tailTrace_464945
  have hstable : (prefixWord ++ tailWord_464945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464945).length < 2 ^ (prefixWord ++ tailWord_464945).sum := by decide
  have hdescent : baseEnd_464945 < baseStart_464945 := by decide
  rcases family_descends (prefixWord ++ tailWord_464945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464951 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 7]
def baseStart_464951 : Nat := 118140960795 + 464951 * 2 ^ 59
def prefixEnd_464951 : Nat := 4983230072969 + 3 ^ 40 * 464951 * 2
def baseEnd_464951 : Nat := 26527038198746178974915

theorem tailTrace_464951 : CollatzResearch.WordTrace tailWord_464951 prefixEnd_464951 26527038198746178974915 := by
  unfold tailWord_464951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958156138569409153970707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11305437425712939435980471 16958156138569409153970707)
  ·
    refine ⟨25437234207854113730956061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16958156138569409153970707 25437234207854113730956061)
    ·
      refine ⟨9538962827945292649108523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25437234207854113730956061 9538962827945292649108523)
      ·
        refine ⟨14308444241917938973662785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538962827945292649108523 14308444241917938973662785)
        ·
          refine ⟨10731333181438454230247089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14308444241917938973662785 10731333181438454230247089)
          ·
            refine ⟨8048499886078840672685317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10731333181438454230247089 8048499886078840672685317)
            ·
              refine ⟨1509093728639782626128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8048499886078840672685317 1509093728639782626128497)
              ·
                refine ⟨1131820296479836969596373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509093728639782626128497 1131820296479836969596373)
                ·
                  refine ⟨26527038198746178974915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1131820296479836969596373 26527038198746178974915)
                  ·
                    rfl

theorem cell23_464951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 7].length) (baseStart_464951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464951 prefixEnd_464951 := by exact prefixLift 464951
  have htrace : WordTrace (prefixWord ++ tailWord_464951) baseStart_464951 baseEnd_464951 := by
    simpa [prefixWord, tailWord_464951, baseEnd_464951] using wordTrace_append hprefix tailTrace_464951
  have hstable : (prefixWord ++ tailWord_464951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464951).length < 2 ^ (prefixWord ++ tailWord_464951).sum := by decide
  have hdescent : baseEnd_464951 < baseStart_464951 := by decide
  rcases family_descends (prefixWord ++ tailWord_464951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464968 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 5]
def baseStart_464968 : Nat := 118140960795 + 464968 * 2 ^ 59
def prefixEnd_464968 : Nat := 4983230072969 + 3 ^ 40 * 464968 * 2
def baseEnd_464968 : Nat := 26528008106649116029073

theorem tailTrace_464968 : CollatzResearch.WordTrace tailWord_464968 prefixEnd_464968 26528008106649116029073 := by
  unfold tailWord_464968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479388089753910528669779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11305850786338547371559705 8479388089753910528669779)
  ·
    refine ⟨12719082134630865793004669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479388089753910528669779 12719082134630865793004669)
    ·
      refine ⟨4769655800486574672376751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12719082134630865793004669 4769655800486574672376751)
      ·
        refine ⟨7154483700729862008565127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769655800486574672376751 7154483700729862008565127)
        ·
          refine ⟨10731725551094793012847691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154483700729862008565127 10731725551094793012847691)
          ·
            refine ⟨16097588326642189519271537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731725551094793012847691 16097588326642189519271537)
            ·
              refine ⟨12073191244981642139453653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097588326642189519271537 12073191244981642139453653)
              ·
                refine ⟨282965419804257237643445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12073191244981642139453653 282965419804257237643445)
                ·
                  refine ⟨26528008106649116029073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282965419804257237643445 26528008106649116029073)
                  ·
                    rfl

theorem cell23_464968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 5].length) (baseStart_464968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464968 prefixEnd_464968 := by exact prefixLift 464968
  have htrace : WordTrace (prefixWord ++ tailWord_464968) baseStart_464968 baseEnd_464968 := by
    simpa [prefixWord, tailWord_464968, baseEnd_464968] using wordTrace_append hprefix tailTrace_464968
  have hstable : (prefixWord ++ tailWord_464968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464968).length < 2 ^ (prefixWord ++ tailWord_464968).sum := by decide
  have hdescent : baseEnd_464968 < baseStart_464968 := by decide
  rcases family_descends (prefixWord ++ tailWord_464968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464985 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 5]
def baseStart_464985 : Nat := 118140960795 + 464985 * 2 ^ 59
def prefixEnd_464985 : Nat := 4983230072969 + 3 ^ 40 * 464985 * 2
def baseEnd_464985 : Nat := 26528978014552053083231

theorem tailTrace_464985 : CollatzResearch.WordTrace tailWord_464985 prefixEnd_464985 26528978014552053083231 := by
  unfold tailWord_464985
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959396220446232960708409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11306264146964155307138939 16959396220446232960708409)
  ·
    refine ⟨12719547165334674720531307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16959396220446232960708409 12719547165334674720531307)
    ·
      refine ⟨19079320748002012080796961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719547165334674720531307 19079320748002012080796961)
      ·
        refine ⟨14309490561001509060597721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19079320748002012080796961 14309490561001509060597721)
        ·
          refine ⟨10732117920751131795448291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14309490561001509060597721 10732117920751131795448291)
          ·
            refine ⟨16098176881126697693172437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732117920751131795448291 16098176881126697693172437)
            ·
              refine ⟨377301020651406977183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16098176881126697693172437 377301020651406977183729)
              ·
                refine ⟨282975765488555232887797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377301020651406977183729 282975765488555232887797)
                ·
                  refine ⟨26528978014552053083231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282975765488555232887797 26528978014552053083231)
                  ·
                    rfl

theorem cell23_464985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 5].length) (baseStart_464985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464985 prefixEnd_464985 := by exact prefixLift 464985
  have htrace : WordTrace (prefixWord ++ tailWord_464985) baseStart_464985 baseEnd_464985 := by
    simpa [prefixWord, tailWord_464985, baseEnd_464985] using wordTrace_append hprefix tailTrace_464985
  have hstable : (prefixWord ++ tailWord_464985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464985).length < 2 ^ (prefixWord ++ tailWord_464985).sum := by decide
  have hdescent : baseEnd_464985 < baseStart_464985 := by decide
  rcases family_descends (prefixWord ++ tailWord_464985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464990 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_464990 : Nat := 118140960795 + 464990 * 2 ^ 59
def prefixEnd_464990 : Nat := 4983230072969 + 3 ^ 40 * 464990 * 2
def baseEnd_464990 : Nat := 238763369534240958186557

theorem tailTrace_464990 : CollatzResearch.WordTrace tailWord_464990 prefixEnd_464990 238763369534240958186557 := by
  unfold tailWord_464990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119947323178514851830053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11306385723618745876426949 2119947323178514851830053)
  ·
    refine ⟨397490123095971534718135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2119947323178514851830053 397490123095971534718135)
    ·
      refine ⟨596235184643957302077203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397490123095971534718135 596235184643957302077203)
      ·
        refine ⟨894352776965935953115805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596235184643957302077203 894352776965935953115805)
        ·
          refine ⟨335382291362225982418427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894352776965935953115805 335382291362225982418427)
          ·
            refine ⟨503073437043338973627641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335382291362225982418427 503073437043338973627641)
            ·
              refine ⟨377305077782504230220731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503073437043338973627641 377305077782504230220731)
              ·
                refine ⟨565957616673756345331097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377305077782504230220731 565957616673756345331097)
                ·
                  refine ⟨424468212505317258998323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565957616673756345331097 424468212505317258998323)
                  ·
                    refine ⟨636702318757975888497485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424468212505317258998323 636702318757975888497485)
                    ·
                      refine ⟨238763369534240958186557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636702318757975888497485 238763369534240958186557)
                      ·
                        rfl

theorem cell23_464990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_464990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_464990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_464990 prefixEnd_464990 := by exact prefixLift 464990
  have htrace : WordTrace (prefixWord ++ tailWord_464990) baseStart_464990 baseEnd_464990 := by
    simpa [prefixWord, tailWord_464990, baseEnd_464990] using wordTrace_append hprefix tailTrace_464990
  have hstable : (prefixWord ++ tailWord_464990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464990).length < 2 ^ (prefixWord ++ tailWord_464990).sum := by decide
  have hdescent : baseEnd_464990 < baseStart_464990 := by decide
  rcases family_descends (prefixWord ++ tailWord_464990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465085 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_465085 : Nat := 118140960795 + 465085 * 2 ^ 59
def prefixEnd_465085 : Nat := 4983230072969 + 3 ^ 40 * 465085 * 2
def baseEnd_465085 : Nat := 238812150196418086498619

theorem tailTrace_465085 : CollatzResearch.WordTrace tailWord_465085 prefixEnd_465085 238812150196418086498619 := by
  unfold tailWord_465085
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963043520083950039348709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11308695680055966692899139 16963043520083950039348709)
  ·
    refine ⟨3180570660015740632377883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16963043520083950039348709 3180570660015740632377883)
    ·
      refine ⟨4770855990023610948566825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180570660015740632377883 4770855990023610948566825)
      ·
        refine ⟨3578141992517708211425119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4770855990023610948566825 3578141992517708211425119)
        ·
          refine ⟨5367212988776562317137679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578141992517708211425119 5367212988776562317137679)
          ·
            refine ⟨8050819483164843475706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367212988776562317137679 8050819483164843475706519)
            ·
              refine ⟨12076229224747265213559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8050819483164843475706519 12076229224747265213559779)
              ·
                refine ⟨18114343837120897820339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12076229224747265213559779 18114343837120897820339669)
                ·
                  refine ⟨424554933682521042664211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18114343837120897820339669 424554933682521042664211)
                  ·
                    refine ⟨636832400523781563996317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424554933682521042664211 636832400523781563996317)
                    ·
                      refine ⟨238812150196418086498619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636832400523781563996317 238812150196418086498619)
                      ·
                        rfl

theorem cell23_465085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_465085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465085 prefixEnd_465085 := by exact prefixLift 465085
  have htrace : WordTrace (prefixWord ++ tailWord_465085) baseStart_465085 baseEnd_465085 := by
    simpa [prefixWord, tailWord_465085, baseEnd_465085] using wordTrace_append hprefix tailTrace_465085
  have hstable : (prefixWord ++ tailWord_465085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465085).length < 2 ^ (prefixWord ++ tailWord_465085).sum := by decide
  have hdescent : baseEnd_465085 < baseStart_465085 := by decide
  rcases family_descends (prefixWord ++ tailWord_465085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465092 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 6]
def baseStart_465092 : Nat := 118140960795 + 465092 * 2 ^ 59
def prefixEnd_465092 : Nat := 4983230072969 + 3 ^ 40 * 465092 * 2
def baseEnd_465092 : Nat := 26535082728999951012343

theorem tailTrace_465092 : CollatzResearch.WordTrace tailWord_465092 prefixEnd_465092 26535082728999951012343 := by
  unfold tailWord_465092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481649415529295117426765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11308865887372393489902353 8481649415529295117426765)
  ·
    refine ⟨3180618530823485669035037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8481649415529295117426765 3180618530823485669035037)
    ·
      refine ⟨1192731949058807125888139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3180618530823485669035037 1192731949058807125888139)
      ·
        refine ⟨1789097923588210688832209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192731949058807125888139 1789097923588210688832209)
        ·
          refine ⟨1341823442691158016624157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789097923588210688832209 1341823442691158016624157)
          ·
            refine ⟨503183791009184256234059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1341823442691158016624157 503183791009184256234059)
            ·
              refine ⟨754775686513776384351089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503183791009184256234059 754775686513776384351089)
              ·
                refine ⟨566081764885332288263317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754775686513776384351089 566081764885332288263317)
                ·
                  refine ⟨26535082728999951012343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 566081764885332288263317 26535082728999951012343)
                  ·
                    rfl

theorem cell23_465092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_465092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465092 prefixEnd_465092 := by exact prefixLift 465092
  have htrace : WordTrace (prefixWord ++ tailWord_465092) baseStart_465092 baseEnd_465092 := by
    simpa [prefixWord, tailWord_465092, baseEnd_465092] using wordTrace_append hprefix tailTrace_465092
  have hstable : (prefixWord ++ tailWord_465092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465092).length < 2 ^ (prefixWord ++ tailWord_465092).sum := by decide
  have hdescent : baseEnd_465092 < baseStart_465092 := by decide
  rcases family_descends (prefixWord ++ tailWord_465092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465102 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_465102 : Nat := 118140960795 + 465102 * 2 ^ 59
def prefixEnd_465102 : Nat := 4983230072969 + 3 ^ 40 * 465102 * 2
def baseEnd_465102 : Nat := 238820879367544519986041

theorem tailTrace_465102 : CollatzResearch.WordTrace tailWord_465102 prefixEnd_465102 238820879367544519986041 := by
  unfold tailWord_465102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120457945127795242839695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11309109040681574628478373 2120457945127795242839695)
  ·
    refine ⟨3180686917691692864259543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120457945127795242839695 3180686917691692864259543)
    ·
      refine ⟨4771030376537539296389315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180686917691692864259543 4771030376537539296389315)
      ·
        refine ⟨7156545564806308944583973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771030376537539296389315 7156545564806308944583973)
        ·
          refine ⟨1341852293401182927109495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7156545564806308944583973 1341852293401182927109495)
          ·
            refine ⟨2012778440101774390664243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341852293401182927109495 2012778440101774390664243)
            ·
              refine ⟨3019167660152661585996365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012778440101774390664243 3019167660152661585996365)
              ·
                refine ⟨1132187872557248094748637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3019167660152661585996365 1132187872557248094748637)
                ·
                  refine ⟨424570452208968035530739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132187872557248094748637 424570452208968035530739)
                  ·
                    refine ⟨636855678313452053296109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424570452208968035530739 636855678313452053296109)
                    ·
                      refine ⟨238820879367544519986041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 636855678313452053296109 238820879367544519986041)
                      ·
                        rfl

theorem cell23_465102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_465102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465102 prefixEnd_465102 := by exact prefixLift 465102
  have htrace : WordTrace (prefixWord ++ tailWord_465102) baseStart_465102 baseEnd_465102 := by
    simpa [prefixWord, tailWord_465102, baseEnd_465102] using wordTrace_append hprefix tailTrace_465102
  have hstable : (prefixWord ++ tailWord_465102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465102).length < 2 ^ (prefixWord ++ tailWord_465102).sum := by decide
  have hdescent : baseEnd_465102 < baseStart_465102 := by decide
  rcases family_descends (prefixWord ++ tailWord_465102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465135 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 4, 4]
def baseStart_465135 : Nat := 118140960795 + 465135 * 2 ^ 59
def prefixEnd_465135 : Nat := 4983230072969 + 3 ^ 40 * 465135 * 2
def baseEnd_465135 : Nat := 79612608076380963624463

theorem tailTrace_465135 : CollatzResearch.WordTrace tailWord_465135 prefixEnd_465135 79612608076380963624463 := by
  unfold tailWord_465135
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964867169902808578668859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309911446601872385779239 16964867169902808578668859)
  ·
    refine ⟨25447300754854212868003289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964867169902808578668859 25447300754854212868003289)
    ·
      refine ⟨19085475566140659651002467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25447300754854212868003289 19085475566140659651002467)
      ·
        refine ⟨28628213349210989476503701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19085475566140659651002467 28628213349210989476503701)
        ·
          refine ⟨1341947500744265131711111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28628213349210989476503701 1341947500744265131711111)
          ·
            refine ⟨2012921251116397697566667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341947500744265131711111 2012921251116397697566667)
            ·
              refine ⟨3019381876674596546350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012921251116397697566667 3019381876674596546350001)
              ·
                refine ⟨2264536407505947409762501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019381876674596546350001 2264536407505947409762501)
                ·
                  refine ⟨424600576407365139330469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264536407505947409762501 424600576407365139330469)
                  ·
                    refine ⟨79612608076380963624463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424600576407365139330469 79612608076380963624463)
                    ·
                      rfl

theorem cell23_465135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_465135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465135 prefixEnd_465135 := by exact prefixLift 465135
  have htrace : WordTrace (prefixWord ++ tailWord_465135) baseStart_465135 baseEnd_465135 := by
    simpa [prefixWord, tailWord_465135, baseEnd_465135] using wordTrace_append hprefix tailTrace_465135
  have hstable : (prefixWord ++ tailWord_465135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465135).length < 2 ^ (prefixWord ++ tailWord_465135).sum := by decide
  have hdescent : baseEnd_465135 < baseStart_465135 := by decide
  rcases family_descends (prefixWord ++ tailWord_465135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465142 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_465142 : Nat := 118140960795 + 465142 * 2 ^ 59
def prefixEnd_465142 : Nat := 4983230072969 + 3 ^ 40 * 465142 * 2
def baseEnd_465142 : Nat := 238841418593724363485857

theorem tailTrace_465142 : CollatzResearch.WordTrace tailWord_465142 prefixEnd_465142 238841418593724363485857 := by
  unfold tailWord_465142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060320155054840548385855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11310081653918299182782453 1060320155054840548385855)
  ·
    refine ⟨1590480232582260822578783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1060320155054840548385855 1590480232582260822578783)
    ·
      refine ⟨2385720348873391233868175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590480232582260822578783 2385720348873391233868175)
      ·
        refine ⟨3578580523310086850802263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385720348873391233868175 3578580523310086850802263)
        ·
          refine ⟨5367870784965130276203395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578580523310086850802263 5367870784965130276203395)
          ·
            refine ⟨8051806177447695414305093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367870784965130276203395 8051806177447695414305093)
            ·
              refine ⟨1509713658271442890182205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8051806177447695414305093 1509713658271442890182205)
              ·
                refine ⟨566142621851791083818327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509713658271442890182205 566142621851791083818327)
                ·
                  refine ⟨849213932777686625727491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566142621851791083818327 849213932777686625727491)
                  ·
                    refine ⟨1273820899166529938591237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849213932777686625727491 1273820899166529938591237)
                    ·
                      refine ⟨238841418593724363485857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1273820899166529938591237 238841418593724363485857)
                      ·
                        rfl

theorem cell23_465142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_465142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465142 prefixEnd_465142 := by exact prefixLift 465142
  have htrace : WordTrace (prefixWord ++ tailWord_465142) baseStart_465142 baseEnd_465142 := by
    simpa [prefixWord, tailWord_465142, baseEnd_465142] using wordTrace_append hprefix tailTrace_465142
  have hstable : (prefixWord ++ tailWord_465142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465142).length < 2 ^ (prefixWord ++ tailWord_465142).sum := by decide
  have hdescent : baseEnd_465142 < baseStart_465142 := by decide
  rcases family_descends (prefixWord ++ tailWord_465142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465148 : List Nat := [2, 2, 2, 1, 4, 1, 11]
def baseStart_465148 : Nat := 118140960795 + 465148 * 2 ^ 59
def prefixEnd_465148 : Nat := 4983230072969 + 3 ^ 40 * 465148 * 2
def baseEnd_465148 : Nat := 2948697524415448642109

theorem tailTrace_465148 : CollatzResearch.WordTrace tailWord_465148 prefixEnd_465148 2948697524415448642109 := by
  unfold tailWord_465148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482670659427855899446049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11310227545903807865928065 8482670659427855899446049)
  ·
    refine ⟨6362002994570891924584537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8482670659427855899446049 6362002994570891924584537)
    ·
      refine ⟨4771502245928168943438403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6362002994570891924584537 4771502245928168943438403)
      ·
        refine ⟨7157253368892253415157605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771502245928168943438403 7157253368892253415157605)
        ·
          refine ⟨1341985006667297515342051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7157253368892253415157605 1341985006667297515342051)
          ·
            refine ⟨2012977510000946273013077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341985006667297515342051 2012977510000946273013077)
            ·
              refine ⟨2948697524415448642109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2012977510000946273013077 2948697524415448642109)
              ·
                rfl

theorem cell23_465148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 11].length) (baseStart_465148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465148 prefixEnd_465148 := by exact prefixLift 465148
  have htrace : WordTrace (prefixWord ++ tailWord_465148) baseStart_465148 baseEnd_465148 := by
    simpa [prefixWord, tailWord_465148, baseEnd_465148] using wordTrace_append hprefix tailTrace_465148
  have hstable : (prefixWord ++ tailWord_465148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465148).length < 2 ^ (prefixWord ++ tailWord_465148).sum := by decide
  have hdescent : baseEnd_465148 < baseStart_465148 := by decide
  rcases family_descends (prefixWord ++ tailWord_465148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465169 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_465169 : Nat := 118140960795 + 465169 * 2 ^ 59
def prefixEnd_465169 : Nat := 4983230072969 + 3 ^ 40 * 465169 * 2
def baseEnd_465169 : Nat := 79618427523798585949411

theorem tailTrace_465169 : CollatzResearch.WordTrace tailWord_465169 prefixEnd_465169 79618427523798585949411 := by
  unfold tailWord_465169
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966107251779632385406561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11310738167853088256937707 16966107251779632385406561)
  ·
    refine ⟨12724580438834724289054921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16966107251779632385406561 12724580438834724289054921)
    ·
      refine ⟨9543435329126043216791191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12724580438834724289054921 9543435329126043216791191)
      ·
        refine ⟨14315152993689064825186787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543435329126043216791191 14315152993689064825186787)
        ·
          refine ⟨21472729490533597237780181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315152993689064825186787 21472729490533597237780181)
          ·
            refine ⟨503267097434381185260473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21472729490533597237780181 503267097434381185260473)
            ·
              refine ⟨377450323075785888945355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503267097434381185260473 377450323075785888945355)
              ·
                refine ⟨566175484613678833418033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377450323075785888945355 566175484613678833418033)
                ·
                  refine ⟨424631613460259125063525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566175484613678833418033 424631613460259125063525)
                  ·
                    refine ⟨79618427523798585949411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424631613460259125063525 79618427523798585949411)
                    ·
                      rfl

theorem cell23_465169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_465169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465169 prefixEnd_465169 := by exact prefixLift 465169
  have htrace : WordTrace (prefixWord ++ tailWord_465169) baseStart_465169 baseEnd_465169 := by
    simpa [prefixWord, tailWord_465169, baseEnd_465169] using wordTrace_append hprefix tailTrace_465169
  have hstable : (prefixWord ++ tailWord_465169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465169).length < 2 ^ (prefixWord ++ tailWord_465169).sum := by decide
  have hdescent : baseEnd_465169 < baseStart_465169 := by decide
  rcases family_descends (prefixWord ++ tailWord_465169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465182 : List Nat := [4, 3, 2, 1, 1, 1, 2, 9]
def baseStart_465182 : Nat := 118140960795 + 465182 * 2 ^ 59
def prefixEnd_465182 : Nat := 4983230072969 + 3 ^ 40 * 465182 * 2
def baseEnd_465182 : Nat := 8846739178514970629099

theorem tailTrace_465182 : CollatzResearch.WordTrace tailWord_465182 prefixEnd_465182 8846739178514970629099 := by
  unfold tailWord_465182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120822675091566950703725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11311054267155023737086533 2120822675091566950703725)
  ·
    refine ⟨795308503159337606513897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2120822675091566950703725 795308503159337606513897)
    ·
      refine ⟨596481377369503204885423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 795308503159337606513897 596481377369503204885423)
      ·
        refine ⟨894722066054254807328135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596481377369503204885423 894722066054254807328135)
        ·
          refine ⟨1342083099081382210992203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894722066054254807328135 1342083099081382210992203)
          ·
            refine ⟨2013124648622073316488305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342083099081382210992203 2013124648622073316488305)
            ·
              refine ⟨1509843486466554987366229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013124648622073316488305 1509843486466554987366229)
              ·
                refine ⟨8846739178514970629099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1509843486466554987366229 8846739178514970629099)
                ·
                  rfl

theorem cell23_465182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_465182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465182 prefixEnd_465182 := by exact prefixLift 465182
  have htrace : WordTrace (prefixWord ++ tailWord_465182) baseStart_465182 baseEnd_465182 := by
    simpa [prefixWord, tailWord_465182, baseEnd_465182] using wordTrace_append hprefix tailTrace_465182
  have hstable : (prefixWord ++ tailWord_465182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465182).length < 2 ^ (prefixWord ++ tailWord_465182).sum := by decide
  have hdescent : baseEnd_465182 < baseStart_465182 := by decide
  rcases family_descends (prefixWord ++ tailWord_465182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465209 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_465209 : Nat := 118140960795 + 465209 * 2 ^ 59
def prefixEnd_465209 : Nat := 4983230072969 + 3 ^ 40 * 465209 * 2
def baseEnd_465209 : Nat := 238875821797575601348049

theorem tailTrace_465209 : CollatzResearch.WordTrace tailWord_465209 prefixEnd_465209 238875821797575601348049 := by
  unfold tailWord_465209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967566171634719216862681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11311710781089812811241787 16967566171634719216862681)
  ·
    refine ⟨12725674628726039412647011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16967566171634719216862681 12725674628726039412647011)
    ·
      refine ⟨19088511943089059118970517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725674628726039412647011 19088511943089059118970517)
      ·
        refine ⟨894773997332299646201743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19088511943089059118970517 894773997332299646201743)
        ·
          refine ⟨1342160995998449469302615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894773997332299646201743 1342160995998449469302615)
          ·
            refine ⟨2013241493997674203953923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342160995998449469302615 2013241493997674203953923)
            ·
              refine ⟨3019862240996511305930885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013241493997674203953923 3019862240996511305930885)
              ·
                refine ⟨566224170186845869862041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3019862240996511305930885 566224170186845869862041)
                ·
                  refine ⟨424668127640134402396531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566224170186845869862041 424668127640134402396531)
                  ·
                    refine ⟨637002191460201603594797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 424668127640134402396531 637002191460201603594797)
                    ·
                      refine ⟨238875821797575601348049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637002191460201603594797 238875821797575601348049)
                      ·
                        rfl

theorem cell23_465209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_465209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465209 prefixEnd_465209 := by exact prefixLift 465209
  have htrace : WordTrace (prefixWord ++ tailWord_465209) baseStart_465209 baseEnd_465209 := by
    simpa [prefixWord, tailWord_465209, baseEnd_465209] using wordTrace_append hprefix tailTrace_465209
  have hstable : (prefixWord ++ tailWord_465209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465209).length < 2 ^ (prefixWord ++ tailWord_465209).sum := by decide
  have hdescent : baseEnd_465209 < baseStart_465209 := by decide
  rcases family_descends (prefixWord ++ tailWord_465209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465232 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2]
def baseStart_465232 : Nat := 118140960795 + 465232 * 2 ^ 59
def prefixEnd_465232 : Nat := 4983230072969 + 3 ^ 40 * 465232 * 2
def baseEnd_465232 : Nat := 238887631852629011360443

theorem tailTrace_465232 : CollatzResearch.WordTrace tailWord_465232 prefixEnd_465232 238887631852629011360443 := by
  unfold tailWord_465232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484202525275697072474975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11312270033700929429966633 8484202525275697072474975)
  ·
    refine ⟨12726303787913545608712463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8484202525275697072474975 12726303787913545608712463)
    ·
      refine ⟨19089455681870318413068695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726303787913545608712463 19089455681870318413068695)
      ·
        refine ⟨28634183522805477619603043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19089455681870318413068695 28634183522805477619603043)
        ·
          refine ⟨42951275284208216429404565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28634183522805477619603043 42951275284208216429404565)
          ·
            refine ⟨2013341028947260145128339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42951275284208216429404565 2013341028947260145128339)
            ·
              refine ⟨3020011543420890217692509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013341028947260145128339 3020011543420890217692509)
              ·
                refine ⟨1132504328782833831634691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3020011543420890217692509 1132504328782833831634691)
                ·
                  refine ⟨1698756493174250747452037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1132504328782833831634691 1698756493174250747452037)
                  ·
                    refine ⟨318516842470172015147257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1698756493174250747452037 318516842470172015147257)
                    ·
                      refine ⟨238887631852629011360443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318516842470172015147257 238887631852629011360443)
                      ·
                        rfl

theorem cell23_465232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 4, 2].length) (baseStart_465232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465232 prefixEnd_465232 := by exact prefixLift 465232
  have htrace : WordTrace (prefixWord ++ tailWord_465232) baseStart_465232 baseEnd_465232 := by
    simpa [prefixWord, tailWord_465232, baseEnd_465232] using wordTrace_append hprefix tailTrace_465232
  have hstable : (prefixWord ++ tailWord_465232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465232).length < 2 ^ (prefixWord ++ tailWord_465232).sum := by decide
  have hdescent : baseEnd_465232 < baseStart_465232 := by decide
  rcases family_descends (prefixWord ++ tailWord_465232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465266 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_465266 : Nat := 118140960795 + 465266 * 2 ^ 59
def prefixEnd_465266 : Nat := 4983230072969 + 3 ^ 40 * 465266 * 2
def baseEnd_465266 : Nat := 238905090194881878335287

theorem tailTrace_465266 : CollatzResearch.WordTrace tailWord_465266 prefixEnd_465266 238905090194881878335287 := by
  unfold tailWord_465266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242411283107054487921913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11313096754952145301125101 4242411283107054487921913)
  ·
    refine ⟨3181808462330290865941435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4242411283107054487921913 3181808462330290865941435)
    ·
      refine ⟨4772712693495436298912153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181808462330290865941435 4772712693495436298912153)
      ·
        refine ⟨3579534520121577224184115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4772712693495436298912153 3579534520121577224184115)
        ·
          refine ⟨5369301780182365836276173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579534520121577224184115 5369301780182365836276173)
          ·
            refine ⟨2013488167568387188603565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5369301780182365836276173 2013488167568387188603565)
            ·
              refine ⟨755058062838145195726337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2013488167568387188603565 755058062838145195726337)
              ·
                refine ⟨566293547128608896794753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755058062838145195726337 566293547128608896794753)
                ·
                  refine ⟨424720160346456672596065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566293547128608896794753 424720160346456672596065)
                  ·
                    refine ⟨318540120259842504447049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424720160346456672596065 318540120259842504447049)
                    ·
                      refine ⟨238905090194881878335287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318540120259842504447049 238905090194881878335287)
                      ·
                        rfl

theorem cell23_465266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_465266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465266 prefixEnd_465266 := by exact prefixLift 465266
  have htrace : WordTrace (prefixWord ++ tailWord_465266) baseStart_465266 baseEnd_465266 := by
    simpa [prefixWord, tailWord_465266, baseEnd_465266] using wordTrace_append hprefix tailTrace_465266
  have hstable : (prefixWord ++ tailWord_465266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465266).length < 2 ^ (prefixWord ++ tailWord_465266).sum := by decide
  have hdescent : baseEnd_465266 < baseStart_465266 := by decide
  rcases family_descends (prefixWord ++ tailWord_465266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465283 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 2, 2, 2]
def baseStart_465283 : Nat := 118140960795 + 465283 * 2 ^ 59
def prefixEnd_465283 : Nat := 4983230072969 + 3 ^ 40 * 465283 * 2
def baseEnd_465283 : Nat := 238913819366008311822709

theorem tailTrace_465283 : CollatzResearch.WordTrace tailWord_465283 prefixEnd_465283 238913819366008311822709 := by
  unfold tailWord_465283
  simp only [CollatzResearch.WordTrace]
  refine ⟨16970265173366629855056503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11313510115577753236704335 16970265173366629855056503)
  ·
    refine ⟨25455397760049944782584755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16970265173366629855056503 25455397760049944782584755)
    ·
      refine ⟨38183096640074917173877133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25455397760049944782584755 38183096640074917173877133)
      ·
        refine ⟨14318661240028093940203925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38183096640074917173877133 14318661240028093940203925)
        ·
          refine ⟨671187245626316903447059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14318661240028093940203925 671187245626316903447059)
          ·
            refine ⟨1006780868439475355170589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671187245626316903447059 1006780868439475355170589)
            ·
              refine ⟨377542825664803258188971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006780868439475355170589 377542825664803258188971)
              ·
                refine ⟨566314238497204887283457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377542825664803258188971 566314238497204887283457)
                ·
                  refine ⟨424735678872903665462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566314238497204887283457 424735678872903665462593)
                  ·
                    refine ⟨318551759154677749096945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 424735678872903665462593 318551759154677749096945)
                    ·
                      refine ⟨238913819366008311822709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318551759154677749096945 238913819366008311822709)
                      ·
                        rfl

theorem cell23_465283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_465283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465283 prefixEnd_465283 := by exact prefixLift 465283
  have htrace : WordTrace (prefixWord ++ tailWord_465283) baseStart_465283 baseEnd_465283 := by
    simpa [prefixWord, tailWord_465283, baseEnd_465283] using wordTrace_append hprefix tailTrace_465283
  have hstable : (prefixWord ++ tailWord_465283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465283).length < 2 ^ (prefixWord ++ tailWord_465283).sum := by decide
  have hdescent : baseEnd_465283 < baseStart_465283 := by decide
  rcases family_descends (prefixWord ++ tailWord_465283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465305 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_465305 : Nat := 118140960795 + 465305 * 2 ^ 59
def prefixEnd_465305 : Nat := 4983230072969 + 3 ^ 40 * 465305 * 2
def baseEnd_465305 : Nat := 238925115940407225747607

theorem tailTrace_465305 : CollatzResearch.WordTrace tailWord_465305 prefixEnd_465305 238925115940407225747607 := by
  unfold tailWord_465305
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971067579286927612357369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314045052857951741571579 16971067579286927612357369)
  ·
    refine ⟨12728300684465195709268027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16971067579286927612357369 12728300684465195709268027)
    ·
      refine ⟨19092451026697793563902041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12728300684465195709268027 19092451026697793563902041)
      ·
        refine ⟨14319338270023345172926531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19092451026697793563902041 14319338270023345172926531)
        ·
          refine ⟨21479007405035017759389797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14319338270023345172926531 21479007405035017759389797)
          ·
            refine ⟨4027313888444065829885587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21479007405035017759389797 4027313888444065829885587)
            ·
              refine ⟨6040970832666098744828381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027313888444065829885587 6040970832666098744828381)
              ·
                refine ⟨2265364062249787029310643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6040970832666098744828381 2265364062249787029310643)
                ·
                  refine ⟨3398046093374680543965965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2265364062249787029310643 3398046093374680543965965)
                  ·
                    refine ⟨1274267285015505203987237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3398046093374680543965965 1274267285015505203987237)
                    ·
                      refine ⟨238925115940407225747607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1274267285015505203987237 238925115940407225747607)
                      ·
                        rfl

theorem cell23_465305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_465305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465305 prefixEnd_465305 := by exact prefixLift 465305
  have htrace : WordTrace (prefixWord ++ tailWord_465305) baseStart_465305 baseEnd_465305 := by
    simpa [prefixWord, tailWord_465305, baseEnd_465305] using wordTrace_append hprefix tailTrace_465305
  have hstable : (prefixWord ++ tailWord_465305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465305).length < 2 ^ (prefixWord ++ tailWord_465305).sum := by decide
  have hdescent : baseEnd_465305 < baseStart_465305 := by decide
  rcases family_descends (prefixWord ++ tailWord_465305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465342 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_465342 : Nat := 118140960795 + 465342 * 2 ^ 59
def prefixEnd_465342 : Nat := 4983230072969 + 3 ^ 40 * 465342 * 2
def baseEnd_465342 : Nat := 238944114724623580984937

theorem tailTrace_465342 : CollatzResearch.WordTrace tailWord_465342 prefixEnd_465342 238944114724623580984937 := by
  unfold tailWord_465342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121552135019110366431785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11314944720101921954302853 2121552135019110366431785)
  ·
    refine ⟨1591164101264332774823839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2121552135019110366431785 1591164101264332774823839)
    ·
      refine ⟨2386746151896499162235759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591164101264332774823839 2386746151896499162235759)
      ·
        refine ⟨3580119227844748743353639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386746151896499162235759 3580119227844748743353639)
        ·
          refine ⟨5370178841767123115030459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580119227844748743353639 5370178841767123115030459)
          ·
            refine ⟨8055268262650684672545689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370178841767123115030459 8055268262650684672545689)
            ·
              refine ⟨6041451196988013504409267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055268262650684672545689 6041451196988013504409267)
              ·
                refine ⟨9062176795482020256613901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041451196988013504409267 9062176795482020256613901)
                ·
                  refine ⟨3398316298305757596230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9062176795482020256613901 3398316298305757596230213)
                  ·
                    refine ⟨637184305932329549293165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3398316298305757596230213 637184305932329549293165)
                    ·
                      refine ⟨238944114724623580984937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637184305932329549293165 238944114724623580984937)
                      ·
                        rfl

theorem cell23_465342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_465342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465342 prefixEnd_465342 := by exact prefixLift 465342
  have htrace : WordTrace (prefixWord ++ tailWord_465342) baseStart_465342 baseEnd_465342 := by
    simpa [prefixWord, tailWord_465342, baseEnd_465342] using wordTrace_append hprefix tailTrace_465342
  have hstable : (prefixWord ++ tailWord_465342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465342).length < 2 ^ (prefixWord ++ tailWord_465342).sum := by decide
  have hdescent : baseEnd_465342 < baseStart_465342 := by decide
  rcases family_descends (prefixWord ++ tailWord_465342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465379 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 6]
def baseStart_465379 : Nat := 118140960795 + 465379 * 2 ^ 59
def prefixEnd_465379 : Nat := 4983230072969 + 3 ^ 40 * 465379 * 2
def baseEnd_465379 : Nat := 26551457056537770691363

theorem tailTrace_465379 : CollatzResearch.WordTrace tailWord_465379 prefixEnd_465379 26551457056537770691363 := by
  unfold tailWord_465379
  simp only [CollatzResearch.WordTrace]
  refine ⟨16973766581018838250551191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11315844387345892167034127 16973766581018838250551191)
  ·
    refine ⟨25460649871528257375826787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16973766581018838250551191 25460649871528257375826787)
    ·
      refine ⟨38190974807292386063740181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25460649871528257375826787 38190974807292386063740181)
      ·
        refine ⟨1790201944091830596737821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38190974807292386063740181 1790201944091830596737821)
        ·
          refine ⟨671325729034436473776683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790201944091830596737821 671325729034436473776683)
          ·
            refine ⟨1006988593551654710665025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671325729034436473776683 1006988593551654710665025)
            ·
              refine ⟨755241445163741032998769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006988593551654710665025 755241445163741032998769)
              ·
                refine ⟨566431083872805774749077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755241445163741032998769 566431083872805774749077)
                ·
                  refine ⟨26551457056537770691363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 566431083872805774749077 26551457056537770691363)
                  ·
                    rfl

theorem cell23_465379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 6].length) (baseStart_465379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465379 prefixEnd_465379 := by exact prefixLift 465379
  have htrace : WordTrace (prefixWord ++ tailWord_465379) baseStart_465379 baseEnd_465379 := by
    simpa [prefixWord, tailWord_465379, baseEnd_465379] using wordTrace_append hprefix tailTrace_465379
  have hstable : (prefixWord ++ tailWord_465379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465379).length < 2 ^ (prefixWord ++ tailWord_465379).sum := by decide
  have hdescent : baseEnd_465379 < baseStart_465379 := by decide
  rcases family_descends (prefixWord ++ tailWord_465379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465410 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_465410 : Nat := 118140960795 + 465410 * 2 ^ 59
def prefixEnd_465410 : Nat := 4983230072969 + 3 ^ 40 * 465410 * 2
def baseEnd_465410 : Nat := 238979031409129314934625

theorem tailTrace_465410 : CollatzResearch.WordTrace tailWord_465410 prefixEnd_465410 238979031409129314934625 := by
  unfold tailWord_465410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243724310976632636232421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11316598162604353696619789 4243724310976632636232421)
  ·
    refine ⟨795698308308118619293579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4243724310976632636232421 795698308308118619293579)
    ·
      refine ⟨1193547462462177928940369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795698308308118619293579 1193547462462177928940369)
      ·
        refine ⟨895160596846633446705277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193547462462177928940369 895160596846633446705277)
        ·
          refine ⟨335685223817487542514479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 895160596846633446705277 335685223817487542514479)
          ·
            refine ⟨503527835726231313771719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335685223817487542514479 503527835726231313771719)
            ·
              refine ⟨755291753589346970657579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503527835726231313771719 755291753589346970657579)
              ·
                refine ⟨1132937630384020455986369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755291753589346970657579 1132937630384020455986369)
                ·
                  refine ⟨849703222788015341989777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132937630384020455986369 849703222788015341989777)
                  ·
                    refine ⟨637277417091011506492333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849703222788015341989777 637277417091011506492333)
                    ·
                      refine ⟨238979031409129314934625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637277417091011506492333 238979031409129314934625)
                      ·
                        rfl

theorem cell23_465410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_465410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465410 prefixEnd_465410 := by exact prefixLift 465410
  have htrace : WordTrace (prefixWord ++ tailWord_465410) baseStart_465410 baseEnd_465410 := by
    simpa [prefixWord, tailWord_465410, baseEnd_465410] using wordTrace_append hprefix tailTrace_465410
  have hstable : (prefixWord ++ tailWord_465410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465410).length < 2 ^ (prefixWord ++ tailWord_465410).sum := by decide
  have hdescent : baseEnd_465410 < baseStart_465410 := by decide
  rcases family_descends (prefixWord ++ tailWord_465410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465429 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_465429 : Nat := 118140960795 + 465429 * 2 ^ 59
def prefixEnd_465429 : Nat := 4983230072969 + 3 ^ 40 * 465429 * 2
def baseEnd_465429 : Nat := 238988787541564740597037

theorem tailTrace_465429 : CollatzResearch.WordTrace tailWord_465429 prefixEnd_465429 238988787541564740597037 := by
  unfold tailWord_465429
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975590230837696789871341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11317060153891797859914227 16975590230837696789871341)
  ·
    refine ⟨6365846336564136296201753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16975590230837696789871341 6365846336564136296201753)
    ·
      refine ⟨4774384752423102222151315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6365846336564136296201753 4774384752423102222151315)
      ·
        refine ⟨7161577128634653333226973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774384752423102222151315 7161577128634653333226973)
        ·
          refine ⟨2685591423237994999960115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7161577128634653333226973 2685591423237994999960115)
          ·
            refine ⟨4028387134856992499940173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685591423237994999960115 4028387134856992499940173)
            ·
              refine ⟨1510645175571372187477565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028387134856992499940173 1510645175571372187477565)
              ·
                refine ⟨566491940839264570304087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1510645175571372187477565 566491940839264570304087)
                ·
                  refine ⟨849737911258896855456131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566491940839264570304087 849737911258896855456131)
                  ·
                    refine ⟨1274606866888345283184197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 849737911258896855456131 1274606866888345283184197)
                    ·
                      refine ⟨238988787541564740597037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1274606866888345283184197 238988787541564740597037)
                      ·
                        rfl

theorem cell23_465429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_465429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465429 prefixEnd_465429 := by exact prefixLift 465429
  have htrace : WordTrace (prefixWord ++ tailWord_465429) baseStart_465429 baseEnd_465429 := by
    simpa [prefixWord, tailWord_465429, baseEnd_465429] using wordTrace_append hprefix tailTrace_465429
  have hstable : (prefixWord ++ tailWord_465429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465429).length < 2 ^ (prefixWord ++ tailWord_465429).sum := by decide
  have hdescent : baseEnd_465429 < baseStart_465429 := by decide
  rcases family_descends (prefixWord ++ tailWord_465429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465442 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_465442 : Nat := 118140960795 + 465442 * 2 ^ 59
def prefixEnd_465442 : Nat := 4983230072969 + 3 ^ 40 * 465442 * 2
def baseEnd_465442 : Nat := 238995462790073189734477

theorem tailTrace_465442 : CollatzResearch.WordTrace tailWord_465442 prefixEnd_465442 238995462790073189734477 := by
  unfold tailWord_465442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244016094947650002523645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11317376253193733340063053 4244016094947650002523645)
  ·
    refine ⟨1591506035605368750946367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4244016094947650002523645 1591506035605368750946367)
    ·
      refine ⟨2387259053408053126419551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591506035605368750946367 2387259053408053126419551)
      ·
        refine ⟨3580888580112079689629327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387259053408053126419551 3580888580112079689629327)
        ·
          refine ⟨5371332870168119534443991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580888580112079689629327 5371332870168119534443991)
          ·
            refine ⟨8056999305252179301665987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371332870168119534443991 8056999305252179301665987)
            ·
              refine ⟨12085498957878268952498981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056999305252179301665987 12085498957878268952498981)
              ·
                refine ⟨2266031054602175428593559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12085498957878268952498981 2266031054602175428593559)
                ·
                  refine ⟨3399046581903263142890339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2266031054602175428593559 3399046581903263142890339)
                  ·
                    refine ⟨5098569872854894714335509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3399046581903263142890339 5098569872854894714335509)
                    ·
                      refine ⟨238995462790073189734477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5098569872854894714335509 238995462790073189734477)
                      ·
                        rfl

theorem cell23_465442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_465442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465442 prefixEnd_465442 := by exact prefixLift 465442
  have htrace : WordTrace (prefixWord ++ tailWord_465442) baseStart_465442 baseEnd_465442 := by
    simpa [prefixWord, tailWord_465442, baseEnd_465442] using wordTrace_append hprefix tailTrace_465442
  have hstable : (prefixWord ++ tailWord_465442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465442).length < 2 ^ (prefixWord ++ tailWord_465442).sum := by decide
  have hdescent : baseEnd_465442 < baseStart_465442 := by decide
  rcases family_descends (prefixWord ++ tailWord_465442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465466 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_465466 : Nat := 118140960795 + 465466 * 2 ^ 59
def prefixEnd_465466 : Nat := 4983230072969 + 3 ^ 40 * 465466 * 2
def baseEnd_465466 : Nat := 239007786325781095834367

theorem tailTrace_465466 : CollatzResearch.WordTrace tailWord_465466 prefixEnd_465466 239007786325781095834367 := by
  unfold tailWord_465466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244234932925913027242063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11317959821135768072645501 4244234932925913027242063)
  ·
    refine ⟨6366352399388869540863095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4244234932925913027242063 6366352399388869540863095)
    ·
      refine ⟨9549528599083304311294643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6366352399388869540863095 9549528599083304311294643)
      ·
        refine ⟨14324292898624956466941965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549528599083304311294643 14324292898624956466941965)
        ·
          refine ⟨5371609836984358675103237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14324292898624956466941965 5371609836984358675103237)
          ·
            refine ⟨1007176844434567251581857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5371609836984358675103237 1007176844434567251581857)
            ·
              refine ⟨755382633325925438686393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007176844434567251581857 755382633325925438686393)
              ·
                refine ⟨566536974994444079014795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755382633325925438686393 566536974994444079014795)
                ·
                  refine ⟨849805462491666118522193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566536974994444079014795 849805462491666118522193)
                  ·
                    refine ⟨637354096868749588891645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 849805462491666118522193 637354096868749588891645)
                    ·
                      refine ⟨239007786325781095834367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637354096868749588891645 239007786325781095834367)
                      ·
                        rfl

theorem cell23_465466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_465466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465466 prefixEnd_465466 := by exact prefixLift 465466
  have htrace : WordTrace (prefixWord ++ tailWord_465466) baseStart_465466 baseEnd_465466 := by
    simpa [prefixWord, tailWord_465466, baseEnd_465466] using wordTrace_append hprefix tailTrace_465466
  have hstable : (prefixWord ++ tailWord_465466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465466).length < 2 ^ (prefixWord ++ tailWord_465466).sum := by decide
  have hdescent : baseEnd_465466 < baseStart_465466 := by decide
  rcases family_descends (prefixWord ++ tailWord_465466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465469 : List Nat := [1, 4, 1, 3, 2, 1, 4, 7]
def baseStart_465469 : Nat := 118140960795 + 465469 * 2 ^ 59
def prefixEnd_465469 : Nat := 4983230072969 + 3 ^ 40 * 465469 * 2
def baseEnd_465469 : Nat := 8852197287694243855439

theorem tailTrace_465469 : CollatzResearch.WordTrace tailWord_465469 prefixEnd_465469 8852197287694243855439 := by
  unfold tailWord_465469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977049150692783621327461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11318032767128522414218307 16977049150692783621327461)
  ·
    refine ⟨3183196715754896928998899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16977049150692783621327461 3183196715754896928998899)
    ·
      refine ⟨4774795073632345393498349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183196715754896928998899 4774795073632345393498349)
      ·
        refine ⟨1790548152612129522561881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4774795073632345393498349 1790548152612129522561881)
        ·
          refine ⟨1342911114459097141921411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790548152612129522561881 1342911114459097141921411)
          ·
            refine ⟨2014366671688645712882117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342911114459097141921411 2014366671688645712882117)
            ·
              refine ⟨377693750941621071165397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2014366671688645712882117 377693750941621071165397)
              ·
                refine ⟨8852197287694243855439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377693750941621071165397 8852197287694243855439)
                ·
                  rfl

theorem cell23_465469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 7].length) (baseStart_465469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465469 prefixEnd_465469 := by exact prefixLift 465469
  have htrace : WordTrace (prefixWord ++ tailWord_465469) baseStart_465469 baseEnd_465469 := by
    simpa [prefixWord, tailWord_465469, baseEnd_465469] using wordTrace_append hprefix tailTrace_465469
  have hstable : (prefixWord ++ tailWord_465469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465469).length < 2 ^ (prefixWord ++ tailWord_465469).sum := by decide
  have hdescent : baseEnd_465469 < baseStart_465469 := by decide
  rcases family_descends (prefixWord ++ tailWord_465469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465536 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2]
def baseStart_465536 : Nat := 118140960795 + 465536 * 2 ^ 59
def prefixEnd_465536 : Nat := 4983230072969 + 3 ^ 40 * 465536 * 2
def baseEnd_465536 : Nat := 239043729971595821959045

theorem tailTrace_465536 : CollatzResearch.WordTrace tailWord_465536 prefixEnd_465536 239043729971595821959045 := by
  unfold tailWord_465536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489746420725027032008231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11319661894300036042677641 8489746420725027032008231)
  ·
    refine ⟨12734619631087540548012347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8489746420725027032008231 12734619631087540548012347)
    ·
      refine ⟨19101929446631310822018521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12734619631087540548012347 19101929446631310822018521)
      ·
        refine ⟨14326447084973483116513891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19101929446631310822018521 14326447084973483116513891)
        ·
          refine ⟨21489670627460224674770837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14326447084973483116513891 21489670627460224674770837)
          ·
            refine ⟨1007328310662198031629883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21489670627460224674770837 1007328310662198031629883)
            ·
              refine ⟨1510992465993297047444825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007328310662198031629883 1510992465993297047444825)
              ·
                refine ⟨1133244349494972785583619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510992465993297047444825 1133244349494972785583619)
                ·
                  refine ⟨1699866524242459178375429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133244349494972785583619 1699866524242459178375429)
                  ·
                    refine ⟨318724973295461095945393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1699866524242459178375429 318724973295461095945393)
                    ·
                      refine ⟨239043729971595821959045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318724973295461095945393 239043729971595821959045)
                      ·
                        rfl

theorem cell23_465536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_465536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465536 prefixEnd_465536 := by exact prefixLift 465536
  have htrace : WordTrace (prefixWord ++ tailWord_465536) baseStart_465536 baseEnd_465536 := by
    simpa [prefixWord, tailWord_465536, baseEnd_465536] using wordTrace_append hprefix tailTrace_465536
  have hstable : (prefixWord ++ tailWord_465536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465536).length < 2 ^ (prefixWord ++ tailWord_465536).sum := by decide
  have hdescent : baseEnd_465536 < baseStart_465536 := by decide
  rcases family_descends (prefixWord ++ tailWord_465536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465540 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_465540 : Nat := 118140960795 + 465540 * 2 ^ 59
def prefixEnd_465540 : Nat := 4983230072969 + 3 ^ 40 * 465540 * 2
def baseEnd_465540 : Nat := 239045783894213806309027

theorem tailTrace_465540 : CollatzResearch.WordTrace tailWord_465540 prefixEnd_465540 239045783894213806309027 := by
  unfold tailWord_465540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489819366717781373581037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11319759155623708498108049 8489819366717781373581037)
  ·
    refine ⟨3183682262519168015092889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8489819366717781373581037 3183682262519168015092889)
    ·
      refine ⟨2387761696889376011319667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3183682262519168015092889 2387761696889376011319667)
      ·
        refine ⟨3581642545334064016979501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387761696889376011319667 3581642545334064016979501)
        ·
          refine ⟨1343115954500274006367313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3581642545334064016979501 1343115954500274006367313)
          ·
            refine ⟨1007336965875205504775485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1343115954500274006367313 1007336965875205504775485)
            ·
              refine ⟨377751362203202064290807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1007336965875205504775485 377751362203202064290807)
              ·
                refine ⟨566627043304803096436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377751362203202064290807 566627043304803096436211)
                ·
                  refine ⟨849940564957204644654317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566627043304803096436211 849940564957204644654317)
                  ·
                    refine ⟨318727711858951741745369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 849940564957204644654317 318727711858951741745369)
                    ·
                      refine ⟨239045783894213806309027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318727711858951741745369 239045783894213806309027)
                      ·
                        rfl

theorem cell23_465540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_465540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465540 prefixEnd_465540 := by exact prefixLift 465540
  have htrace : WordTrace (prefixWord ++ tailWord_465540) baseStart_465540 baseEnd_465540 := by
    simpa [prefixWord, tailWord_465540, baseEnd_465540] using wordTrace_append hprefix tailTrace_465540
  have hstable : (prefixWord ++ tailWord_465540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465540).length < 2 ^ (prefixWord ++ tailWord_465540).sum := by decide
  have hdescent : baseEnd_465540 < baseStart_465540 := by decide
  rcases family_descends (prefixWord ++ tailWord_465540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465556 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_465556 : Nat := 118140960795 + 465556 * 2 ^ 59
def prefixEnd_465556 : Nat := 4983230072969 + 3 ^ 40 * 465556 * 2
def baseEnd_465556 : Nat := 239053999584685743708953

theorem tailTrace_465556 : CollatzResearch.WordTrace tailWord_465556 prefixEnd_465556 239053999584685743708953 := by
  unfold tailWord_465556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490111150688798739872261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11320148200918398319829681 8490111150688798739872261)
  ·
    refine ⟨1591895840754149763726049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8490111150688798739872261 1591895840754149763726049)
    ·
      refine ⟨1193921880565612322794537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591895840754149763726049 1193921880565612322794537)
      ·
        refine ⟨895441410424209242095903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193921880565612322794537 895441410424209242095903)
        ·
          refine ⟨1343162115636313863143855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895441410424209242095903 1343162115636313863143855)
          ·
            refine ⟨2014743173454470794715783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343162115636313863143855 2014743173454470794715783)
            ·
              refine ⟨3022114760181706192073675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014743173454470794715783 3022114760181706192073675)
              ·
                refine ⟨4533172140272559288110513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3022114760181706192073675 4533172140272559288110513)
                ·
                  refine ⟨3399879105204419466082885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4533172140272559288110513 3399879105204419466082885)
                  ·
                    refine ⟨637477332225828649890541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3399879105204419466082885 637477332225828649890541)
                    ·
                      refine ⟨239053999584685743708953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637477332225828649890541 239053999584685743708953)
                      ·
                        rfl

theorem cell23_465556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_465556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465556 prefixEnd_465556 := by exact prefixLift 465556
  have htrace : WordTrace (prefixWord ++ tailWord_465556) baseStart_465556 baseEnd_465556 := by
    simpa [prefixWord, tailWord_465556, baseEnd_465556] using wordTrace_append hprefix tailTrace_465556
  have hstable : (prefixWord ++ tailWord_465556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465556).length < 2 ^ (prefixWord ++ tailWord_465556).sum := by decide
  have hdescent : baseEnd_465556 < baseStart_465556 := by decide
  rcases family_descends (prefixWord ++ tailWord_465556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465566 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_465566 : Nat := 118140960795 + 465566 * 2 ^ 59
def prefixEnd_465566 : Nat := 4983230072969 + 3 ^ 40 * 465566 * 2
def baseEnd_465566 : Nat := 239059134391230704583907

theorem tailTrace_465566 : CollatzResearch.WordTrace tailWord_465566 prefixEnd_465566 239059134391230704583907 := by
  unfold tailWord_465566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122573378917671148451069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11320391354227579458405701 2122573378917671148451069)
  ·
    refine ⟨795965017094126680669151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2122573378917671148451069 795965017094126680669151)
    ·
      refine ⟨1193947525641190021003727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795965017094126680669151 1193947525641190021003727)
      ·
        refine ⟨1790921288461785031505591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193947525641190021003727 1790921288461785031505591)
        ·
          refine ⟨2686381932692677547258387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790921288461785031505591 2686381932692677547258387)
          ·
            refine ⟨4029572899039016320887581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686381932692677547258387 4029572899039016320887581)
            ·
              refine ⟨1511089837139631120332843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4029572899039016320887581 1511089837139631120332843)
              ·
                refine ⟨2266634755709446680499265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511089837139631120332843 2266634755709446680499265)
                ·
                  refine ⟨1699976066782085010374449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266634755709446680499265 1699976066782085010374449)
                  ·
                    refine ⟨1274982050086563757780837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1699976066782085010374449 1274982050086563757780837)
                    ·
                      refine ⟨239059134391230704583907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1274982050086563757780837 239059134391230704583907)
                      ·
                        rfl

theorem cell23_465566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_465566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465566 prefixEnd_465566 := by exact prefixLift 465566
  have htrace : WordTrace (prefixWord ++ tailWord_465566) baseStart_465566 baseEnd_465566 := by
    simpa [prefixWord, tailWord_465566, baseEnd_465566] using wordTrace_append hprefix tailTrace_465566
  have hstable : (prefixWord ++ tailWord_465566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465566).length < 2 ^ (prefixWord ++ tailWord_465566).sum := by decide
  have hdescent : baseEnd_465566 < baseStart_465566 := by decide
  rcases family_descends (prefixWord ++ tailWord_465566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465626 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_465626 : Nat := 118140960795 + 465626 * 2 ^ 59
def prefixEnd_465626 : Nat := 4983230072969 + 3 ^ 40 * 465626 * 2
def baseEnd_465626 : Nat := 239089943230500469833631

theorem tailTrace_465626 : CollatzResearch.WordTrace tailWord_465626 prefixEnd_465626 239089943230500469833631 := by
  unfold tailWord_465626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245693852780999858698183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11321850274082666289861821 4245693852780999858698183)
  ·
    refine ⟨6368540779171499788047275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4245693852780999858698183 6368540779171499788047275)
    ·
      refine ⟨9552811168757249682070913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6368540779171499788047275 9552811168757249682070913)
      ·
        refine ⟨7164608376567937261553185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9552811168757249682070913 7164608376567937261553185)
        ·
          refine ⟨5373456282425952946164889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7164608376567937261553185 5373456282425952946164889)
          ·
            refine ⟨4030092211819464709623667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373456282425952946164889 4030092211819464709623667)
            ·
              refine ⟨6045138317729197064435501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030092211819464709623667 6045138317729197064435501)
              ·
                refine ⟨2266926869148448899163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045138317729197064435501 2266926869148448899163313)
                ·
                  refine ⟨1700195151861336674372485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2266926869148448899163313 1700195151861336674372485)
                  ·
                    refine ⟨318786590974000626444841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1700195151861336674372485 318786590974000626444841)
                    ·
                      refine ⟨239089943230500469833631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318786590974000626444841 239089943230500469833631)
                      ·
                        rfl

theorem cell23_465626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_465626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465626 prefixEnd_465626 := by exact prefixLift 465626
  have htrace : WordTrace (prefixWord ++ tailWord_465626) baseStart_465626 baseEnd_465626 := by
    simpa [prefixWord, tailWord_465626, baseEnd_465626] using wordTrace_append hprefix tailTrace_465626
  have hstable : (prefixWord ++ tailWord_465626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465626).length < 2 ^ (prefixWord ++ tailWord_465626).sum := by decide
  have hdescent : baseEnd_465626 < baseStart_465626 := by decide
  rcases family_descends (prefixWord ++ tailWord_465626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465636 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_465636 : Nat := 118140960795 + 465636 * 2 ^ 59
def prefixEnd_465636 : Nat := 4983230072969 + 3 ^ 40 * 465636 * 2
def baseEnd_465636 : Nat := 79698359345681810236195

theorem tailTrace_465636 : CollatzResearch.WordTrace tailWord_465636 prefixEnd_465636 79698359345681810236195 := by
  unfold tailWord_465636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491570070543885571328381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11322093427391847428437841 8491570070543885571328381)
  ·
    refine ⟨3184338776453957089248143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8491570070543885571328381 3184338776453957089248143)
    ·
      refine ⟨4776508164680935633872215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184338776453957089248143 4776508164680935633872215)
      ·
        refine ⟨7164762247021403450808323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776508164680935633872215 7164762247021403450808323)
        ·
          refine ⟨10747143370532105176212485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164762247021403450808323 10747143370532105176212485)
          ·
            refine ⟨2015089381974769720539841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10747143370532105176212485 2015089381974769720539841)
            ·
              refine ⟨1511317036481077290404881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015089381974769720539841 1511317036481077290404881)
              ·
                refine ⟨1133487777360807967803661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511317036481077290404881 1133487777360807967803661)
                ·
                  refine ⟨425057916510302987926373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133487777360807967803661 425057916510302987926373)
                  ·
                    refine ⟨79698359345681810236195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425057916510302987926373 79698359345681810236195)
                    ·
                      rfl

theorem cell23_465636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_465636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465636 prefixEnd_465636 := by exact prefixLift 465636
  have htrace : WordTrace (prefixWord ++ tailWord_465636) baseStart_465636 baseEnd_465636 := by
    simpa [prefixWord, tailWord_465636, baseEnd_465636] using wordTrace_append hprefix tailTrace_465636
  have hstable : (prefixWord ++ tailWord_465636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465636).length < 2 ^ (prefixWord ++ tailWord_465636).sum := by decide
  have hdescent : baseEnd_465636 < baseStart_465636 := by decide
  rcases family_descends (prefixWord ++ tailWord_465636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465646 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_465646 : Nat := 118140960795 + 465646 * 2 ^ 59
def prefixEnd_465646 : Nat := 4983230072969 + 3 ^ 40 * 465646 * 2
def baseEnd_465646 : Nat := 239100212843590391583539

theorem tailTrace_465646 : CollatzResearch.WordTrace tailWord_465646 prefixEnd_465646 239100212843590391583539 := by
  unfold tailWord_465646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122938108881442856315099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11322336580701028567013861 2122938108881442856315099)
  ·
    refine ⟨3184407163322164284472649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122938108881442856315099 3184407163322164284472649)
    ·
      refine ⟨2388305372491623213354487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3184407163322164284472649 2388305372491623213354487)
      ·
        refine ⟨3582458058737434820031731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388305372491623213354487 3582458058737434820031731)
        ·
          refine ⟨5373687088106152230047597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582458058737434820031731 5373687088106152230047597)
          ·
            refine ⟨2015132658039807086267849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5373687088106152230047597 2015132658039807086267849)
            ·
              refine ⟨1511349493529855314700887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015132658039807086267849 1511349493529855314700887)
              ·
                refine ⟨2267024240294782972051331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511349493529855314700887 2267024240294782972051331)
                ·
                  refine ⟨3400536360442174458076997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2267024240294782972051331 3400536360442174458076997)
                  ·
                    refine ⟨637600567582907710889437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3400536360442174458076997 637600567582907710889437)
                    ·
                      refine ⟨239100212843590391583539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637600567582907710889437 239100212843590391583539)
                      ·
                        rfl

theorem cell23_465646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_465646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465646 prefixEnd_465646 := by exact prefixLift 465646
  have htrace : WordTrace (prefixWord ++ tailWord_465646) baseStart_465646 baseEnd_465646 := by
    simpa [prefixWord, tailWord_465646, baseEnd_465646] using wordTrace_append hprefix tailTrace_465646
  have hstable : (prefixWord ++ tailWord_465646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465646).length < 2 ^ (prefixWord ++ tailWord_465646).sum := by decide
  have hdescent : baseEnd_465646 < baseStart_465646 := by decide
  rcases family_descends (prefixWord ++ tailWord_465646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465666 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_465666 : Nat := 118140960795 + 465666 * 2 ^ 59
def prefixEnd_465666 : Nat := 4983230072969 + 3 ^ 40 * 465666 * 2
def baseEnd_465666 : Nat := 26567831384075590370383

theorem tailTrace_465666 : CollatzResearch.WordTrace tailWord_465666 prefixEnd_465666 26567831384075590370383 := by
  unfold tailWord_465666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246058582744771566562213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11322822887319390844165901 4246058582744771566562213)
  ·
    refine ⟨796135984264644668730415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4246058582744771566562213 796135984264644668730415)
    ·
      refine ⟨1194203976396967003095623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796135984264644668730415 1194203976396967003095623)
      ·
        refine ⟨1791305964595450504643435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194203976396967003095623 1791305964595450504643435)
        ·
          refine ⟨2686958946893175756965153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791305964595450504643435 2686958946893175756965153)
          ·
            refine ⟨2015219210169881817723865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686958946893175756965153 2015219210169881817723865)
            ·
              refine ⟨1511414407627411363292899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015219210169881817723865 1511414407627411363292899)
              ·
                refine ⟨2267121611441117044939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511414407627411363292899 2267121611441117044939349)
                ·
                  refine ⟨26567831384075590370383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2267121611441117044939349 26567831384075590370383)
                  ·
                    rfl

theorem cell23_465666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_465666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465666 prefixEnd_465666 := by exact prefixLift 465666
  have htrace : WordTrace (prefixWord ++ tailWord_465666) baseStart_465666 baseEnd_465666 := by
    simpa [prefixWord, tailWord_465666, baseEnd_465666] using wordTrace_append hprefix tailTrace_465666
  have hstable : (prefixWord ++ tailWord_465666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465666).length < 2 ^ (prefixWord ++ tailWord_465666).sum := by decide
  have hdescent : baseEnd_465666 < baseStart_465666 := by decide
  rcases family_descends (prefixWord ++ tailWord_465666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465679 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 3, 5]
def baseStart_465679 : Nat := 118140960795 + 465679 * 2 ^ 59
def prefixEnd_465679 : Nat := 4983230072969 + 3 ^ 40 * 465679 * 2
def baseEnd_465679 : Nat := 79705719235062920823629

theorem tailTrace_465679 : CollatzResearch.WordTrace tailWord_465679 prefixEnd_465679 79705719235062920823629 := by
  unfold tailWord_465679
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984708479931989486472091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11323138986621326324314727 16984708479931989486472091)
  ·
    refine ⟨25477062719897984229708137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984708479931989486472091 25477062719897984229708137)
    ·
      refine ⟨19107797039923488172281103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25477062719897984229708137 19107797039923488172281103)
      ·
        refine ⟨28661695559885232258421655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107797039923488172281103 28661695559885232258421655)
        ·
          refine ⟨42992543339827848387632483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28661695559885232258421655 42992543339827848387632483)
          ·
            refine ⟨64488815009741772581448725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42992543339827848387632483 64488815009741772581448725)
            ·
              refine ⟨3022913203581645589755409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64488815009741772581448725 3022913203581645589755409)
              ·
                refine ⟨2267184902686234192316557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022913203581645589755409 2267184902686234192316557)
                ·
                  refine ⟨850194338507337822118709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267184902686234192316557 850194338507337822118709)
                  ·
                    refine ⟨79705719235062920823629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 850194338507337822118709 79705719235062920823629)
                    ·
                      rfl

theorem cell23_465679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_465679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465679 prefixEnd_465679 := by exact prefixLift 465679
  have htrace : WordTrace (prefixWord ++ tailWord_465679) baseStart_465679 baseEnd_465679 := by
    simpa [prefixWord, tailWord_465679, baseEnd_465679] using wordTrace_append hprefix tailTrace_465679
  have hstable : (prefixWord ++ tailWord_465679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465679).length < 2 ^ (prefixWord ++ tailWord_465679).sum := by decide
  have hdescent : baseEnd_465679 < baseStart_465679 := by decide
  rcases family_descends (prefixWord ++ tailWord_465679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465696 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_465696 : Nat := 118140960795 + 465696 * 2 ^ 59
def prefixEnd_465696 : Nat := 4983230072969 + 3 ^ 40 * 465696 * 2
def baseEnd_465696 : Nat := 79708628958771731986103

theorem tailTrace_465696 : CollatzResearch.WordTrace tailWord_465696 prefixEnd_465696 79708628958771731986103 := by
  unfold tailWord_465696
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492664260435200694920471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11323552347246934259893961 8492664260435200694920471)
  ·
    refine ⟨12738996390652801042380707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492664260435200694920471 12738996390652801042380707)
    ·
      refine ⟨19108494585979201563571061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738996390652801042380707 19108494585979201563571061)
      ·
        refine ⟨1791421367435550146584787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19108494585979201563571061 1791421367435550146584787)
        ·
          refine ⟨2687132051153325219877181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791421367435550146584787 2687132051153325219877181)
          ·
            refine ⟨1007674519182496957453943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2687132051153325219877181 1007674519182496957453943)
            ·
              refine ⟨1511511778773745436180915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007674519182496957453943 1511511778773745436180915)
              ·
                refine ⟨2267267668160618154271373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511511778773745436180915 2267267668160618154271373)
                ·
                  refine ⟨850225375560231807851765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2267267668160618154271373 850225375560231807851765)
                  ·
                    refine ⟨79708628958771731986103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 850225375560231807851765 79708628958771731986103)
                    ·
                      rfl

theorem cell23_465696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_465696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465696 prefixEnd_465696 := by exact prefixLift 465696
  have htrace : WordTrace (prefixWord ++ tailWord_465696) baseStart_465696 baseEnd_465696 := by
    simpa [prefixWord, tailWord_465696, baseEnd_465696] using wordTrace_append hprefix tailTrace_465696
  have hstable : (prefixWord ++ tailWord_465696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465696).length < 2 ^ (prefixWord ++ tailWord_465696).sum := by decide
  have hdescent : baseEnd_465696 < baseStart_465696 := by decide
  rcases family_descends (prefixWord ++ tailWord_465696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465713 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_465713 : Nat := 118140960795 + 465713 * 2 ^ 59
def prefixEnd_465713 : Nat := 4983230072969 + 3 ^ 40 * 465713 * 2
def baseEnd_465713 : Nat := 79711538682480543148577

theorem tailTrace_465713 : CollatzResearch.WordTrace tailWord_465713 prefixEnd_465713 79711538682480543148577 := by
  unfold tailWord_465713
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985948561808813293209793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11323965707872542195473195 16985948561808813293209793)
  ·
    refine ⟨12739461421356609969907345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16985948561808813293209793 12739461421356609969907345)
    ·
      refine ⟨9554596066017457477430509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12739461421356609969907345 9554596066017457477430509)
      ·
        refine ⟨3582973524756546554036441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9554596066017457477430509 3582973524756546554036441)
        ·
          refine ⟨2687230143567409915527331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3582973524756546554036441 2687230143567409915527331)
          ·
            refine ⟨4030845215351114873290997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687230143567409915527331 4030845215351114873290997)
            ·
              refine ⟨377891738939167019371031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4030845215351114873290997 377891738939167019371031)
              ·
                refine ⟨566837608408750529056547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377891738939167019371031 566837608408750529056547)
                ·
                  refine ⟨850256412613125793584821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566837608408750529056547 850256412613125793584821)
                  ·
                    refine ⟨79711538682480543148577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 850256412613125793584821 79711538682480543148577)
                    ·
                      rfl

theorem cell23_465713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_465713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465713 prefixEnd_465713 := by exact prefixLift 465713
  have htrace : WordTrace (prefixWord ++ tailWord_465713) baseStart_465713 baseEnd_465713 := by
    simpa [prefixWord, tailWord_465713, baseEnd_465713] using wordTrace_append hprefix tailTrace_465713
  have hstable : (prefixWord ++ tailWord_465713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465713).length < 2 ^ (prefixWord ++ tailWord_465713).sum := by decide
  have hdescent : baseEnd_465713 < baseStart_465713 := by decide
  rcases family_descends (prefixWord ++ tailWord_465713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465727 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 1, 1, 3]
def baseStart_465727 : Nat := 118140960795 + 465727 * 2 ^ 59
def prefixEnd_465727 : Nat := 4983230072969 + 3 ^ 40 * 465727 * 2
def baseEnd_465727 : Nat := 239141804776604574670667

theorem tailTrace_465727 : CollatzResearch.WordTrace tailWord_465727 prefixEnd_465727 239141804776604574670667 := by
  unfold tailWord_465727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16986459183758093684219435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11324306122505395789479623 16986459183758093684219435)
  ·
    refine ⟨25479688775637140526329153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16986459183758093684219435 25479688775637140526329153)
    ·
      refine ⟨19109766581727855394746865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25479688775637140526329153 19109766581727855394746865)
      ·
        refine ⟨14332324936295891546060149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19109766581727855394746865 14332324936295891546060149)
        ·
          refine ⟨1343655462777739832443139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14332324936295891546060149 1343655462777739832443139)
          ·
            refine ⟨2015483194166609748664709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343655462777739832443139 2015483194166609748664709)
            ·
              refine ⟨377903098906239327874633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2015483194166609748664709 377903098906239327874633)
              ·
                refine ⟨283427324179679495905975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377903098906239327874633 283427324179679495905975)
                ·
                  refine ⟨425140986269519243858963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283427324179679495905975 425140986269519243858963)
                  ·
                    refine ⟨637711479404278865788445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 425140986269519243858963 637711479404278865788445)
                    ·
                      refine ⟨239141804776604574670667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637711479404278865788445 239141804776604574670667)
                      ·
                        rfl

theorem cell23_465727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_465727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465727 prefixEnd_465727 := by exact prefixLift 465727
  have htrace : WordTrace (prefixWord ++ tailWord_465727) baseStart_465727 baseEnd_465727 := by
    simpa [prefixWord, tailWord_465727, baseEnd_465727] using wordTrace_append hprefix tailTrace_465727
  have hstable : (prefixWord ++ tailWord_465727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465727).length < 2 ^ (prefixWord ++ tailWord_465727).sum := by decide
  have hdescent : baseEnd_465727 < baseStart_465727 := by decide
  rcases family_descends (prefixWord ++ tailWord_465727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465736 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_465736 : Nat := 118140960795 + 465736 * 2 ^ 59
def prefixEnd_465736 : Nat := 4983230072969 + 3 ^ 40 * 465736 * 2
def baseEnd_465736 : Nat := 239146426102495039458125

theorem tailTrace_465736 : CollatzResearch.WordTrace tailWord_465736 prefixEnd_465736 239146426102495039458125 := by
  unfold tailWord_465736
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493393720362744110648531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11324524960483658814198041 8493393720362744110648531)
  ·
    refine ⟨12740090580544116165972797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493393720362744110648531 12740090580544116165972797)
    ·
      refine ⟨4777533967704043562239799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12740090580544116165972797 4777533967704043562239799)
      ·
        refine ⟨7166300951556065343359699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4777533967704043562239799 7166300951556065343359699)
        ·
          refine ⟨10749451427334098015039549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7166300951556065343359699 10749451427334098015039549)
          ·
            refine ⟨4031044285250286755639831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10749451427334098015039549 4031044285250286755639831)
            ·
              refine ⟨6046566427875430133459747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031044285250286755639831 6046566427875430133459747)
              ·
                refine ⟨9069849641813145200189621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046566427875430133459747 9069849641813145200189621)
                ·
                  refine ⟨850298403919982362517777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9069849641813145200189621 850298403919982362517777)
                  ·
                    refine ⟨637723802939986771888333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 850298403919982362517777 637723802939986771888333)
                    ·
                      refine ⟨239146426102495039458125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637723802939986771888333 239146426102495039458125)
                      ·
                        rfl

theorem cell23_465736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_465736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465736 prefixEnd_465736 := by exact prefixLift 465736
  have htrace : WordTrace (prefixWord ++ tailWord_465736) baseStart_465736 baseEnd_465736 := by
    simpa [prefixWord, tailWord_465736, baseEnd_465736] using wordTrace_append hprefix tailTrace_465736
  have hstable : (prefixWord ++ tailWord_465736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465736).length < 2 ^ (prefixWord ++ tailWord_465736).sum := by decide
  have hdescent : baseEnd_465736 < baseStart_465736 := by decide
  rcases family_descends (prefixWord ++ tailWord_465736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465767 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_465767 : Nat := 118140960795 + 465767 * 2 ^ 59
def prefixEnd_465767 : Nat := 4983230072969 + 3 ^ 40 * 465767 * 2
def baseEnd_465767 : Nat := 239162344002784418170483

theorem tailTrace_465767 : CollatzResearch.WordTrace tailWord_465767 prefixEnd_465767 239162344002784418170483 := by
  unfold tailWord_465767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987918103613180515675555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11325278735742120343783703 16987918103613180515675555)
  ·
    refine ⟨25481877155419770773513333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16987918103613180515675555 25481877155419770773513333)
    ·
      refine ⟨2388925983320603510016875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25481877155419770773513333 2388925983320603510016875)
      ·
        refine ⟨3583388974980905265025313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388925983320603510016875 3583388974980905265025313)
        ·
          refine ⟨2687541731235678948768985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583388974980905265025313 2687541731235678948768985)
          ·
            refine ⟨2015656298426759211576739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2687541731235678948768985 2015656298426759211576739)
            ·
              refine ⟨3023484447640138817365109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015656298426759211576739 3023484447640138817365109)
              ·
                refine ⟨283451666966263014127979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3023484447640138817365109 283451666966263014127979)
                ·
                  refine ⟨425177500449394521191969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283451666966263014127979 425177500449394521191969)
                  ·
                    refine ⟨318883125337045890893977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 425177500449394521191969 318883125337045890893977)
                    ·
                      refine ⟨239162344002784418170483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318883125337045890893977 239162344002784418170483)
                      ·
                        rfl

theorem cell23_465767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_465767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465767 prefixEnd_465767 := by exact prefixLift 465767
  have htrace : WordTrace (prefixWord ++ tailWord_465767) baseStart_465767 baseEnd_465767 := by
    simpa [prefixWord, tailWord_465767, baseEnd_465767] using wordTrace_append hprefix tailTrace_465767
  have hstable : (prefixWord ++ tailWord_465767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465767).length < 2 ^ (prefixWord ++ tailWord_465767).sum := by decide
  have hdescent : baseEnd_465767 < baseStart_465767 := by decide
  rcases family_descends (prefixWord ++ tailWord_465767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465794 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_465794 : Nat := 118140960795 + 465794 * 2 ^ 59
def prefixEnd_465794 : Nat := 4983230072969 + 3 ^ 40 * 465794 * 2
def baseEnd_465794 : Nat := 79725402660151937510953

theorem tailTrace_465794 : CollatzResearch.WordTrace tailWord_465794 prefixEnd_465794 79725402660151937510953 := by
  unfold tailWord_465794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247225718628841031727109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11325935249676909417938957 4247225718628841031727109)
  ·
    refine ⟨796354822242907693448833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4247225718628841031727109 796354822242907693448833)
    ·
      refine ⟨597266116682180770086625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796354822242907693448833 597266116682180770086625)
      ·
        refine ⟨447949587511635577564969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597266116682180770086625 447949587511635577564969)
        ·
          refine ⟨335962190633726683173727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447949587511635577564969 335962190633726683173727)
          ·
            refine ⟨503943285950590024760591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335962190633726683173727 503943285950590024760591)
            ·
              refine ⟨755914928925885037140887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503943285950590024760591 755914928925885037140887)
              ·
                refine ⟨1133872393388827555711331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755914928925885037140887 1133872393388827555711331)
                ·
                  refine ⟨1700808590083241333566997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133872393388827555711331 1700808590083241333566997)
                  ·
                    refine ⟨79725402660151937510953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1700808590083241333566997 79725402660151937510953)
                    ·
                      rfl

theorem cell23_465794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_465794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465794 prefixEnd_465794 := by exact prefixLift 465794
  have htrace : WordTrace (prefixWord ++ tailWord_465794) baseStart_465794 baseEnd_465794 := by
    simpa [prefixWord, tailWord_465794, baseEnd_465794] using wordTrace_append hprefix tailTrace_465794
  have hstable : (prefixWord ++ tailWord_465794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465794).length < 2 ^ (prefixWord ++ tailWord_465794).sum := by decide
  have hdescent : baseEnd_465794 < baseStart_465794 := by decide
  rcases family_descends (prefixWord ++ tailWord_465794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465800 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_465800 : Nat := 118140960795 + 465800 * 2 ^ 59
def prefixEnd_465800 : Nat := 4983230072969 + 3 ^ 40 * 465800 * 2
def baseEnd_465800 : Nat := 239179288864382789057831

theorem tailTrace_465800 : CollatzResearch.WordTrace tailWord_465800 prefixEnd_465800 239179288864382789057831 := by
  unfold tailWord_465800
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494560856246813575813427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11326081141662418101084569 8494560856246813575813427)
  ·
    refine ⟨12741841284370220363720141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494560856246813575813427 12741841284370220363720141)
    ·
      refine ⟨4778190481638832636395053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12741841284370220363720141 4778190481638832636395053)
      ·
        refine ⟨1791821430614562238648145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4778190481638832636395053 1791821430614562238648145)
        ·
          refine ⟨1343866072960921678986109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791821430614562238648145 1343866072960921678986109)
          ·
            refine ⟨503949777360345629619791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1343866072960921678986109 503949777360345629619791)
            ·
              refine ⟨755924666040518444429687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503949777360345629619791 755924666040518444429687)
              ·
                refine ⟨1133886999060777666644531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755924666040518444429687 1133886999060777666644531)
                ·
                  refine ⟨1700830498591166499966797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1133886999060777666644531 1700830498591166499966797)
                  ·
                    refine ⟨637811436971687437487549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1700830498591166499966797 637811436971687437487549)
                    ·
                      refine ⟨239179288864382789057831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 637811436971687437487549 239179288864382789057831)
                      ·
                        rfl

theorem cell23_465800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_465800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465800 prefixEnd_465800 := by exact prefixLift 465800
  have htrace : WordTrace (prefixWord ++ tailWord_465800) baseStart_465800 baseEnd_465800 := by
    simpa [prefixWord, tailWord_465800, baseEnd_465800] using wordTrace_append hprefix tailTrace_465800
  have hstable : (prefixWord ++ tailWord_465800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465800).length < 2 ^ (prefixWord ++ tailWord_465800).sum := by decide
  have hdescent : baseEnd_465800 < baseStart_465800 := by decide
  rcases family_descends (prefixWord ++ tailWord_465800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465908 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_465908 : Nat := 118140960795 + 465908 * 2 ^ 59
def prefixEnd_465908 : Nat := 4983230072969 + 3 ^ 40 * 465908 * 2
def baseEnd_465908 : Nat := 239234744775068366507335

theorem tailTrace_465908 : CollatzResearch.WordTrace tailWord_465908 prefixEnd_465908 239234744775068366507335 := by
  unfold tailWord_465908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8496530398051180798279189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11328707197401574397705585 8496530398051180798279189)
  ·
    refine ⟨398274862408649099919337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8496530398051180798279189 398274862408649099919337)
    ·
      refine ⟨298706146806486824939503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398274862408649099919337 298706146806486824939503)
      ·
        refine ⟨448059220209730237409255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298706146806486824939503 448059220209730237409255)
        ·
          refine ⟨672088830314595356113883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448059220209730237409255 672088830314595356113883)
          ·
            refine ⟨1008133245471893034170825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672088830314595356113883 1008133245471893034170825)
            ·
              refine ⟨756099934103919775628119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008133245471893034170825 756099934103919775628119)
              ·
                refine ⟨1134149901155879663442179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756099934103919775628119 1134149901155879663442179)
                ·
                  refine ⟨1701224851733819495163269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134149901155879663442179 1701224851733819495163269)
                  ·
                    refine ⟨318979659700091155343113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1701224851733819495163269 318979659700091155343113)
                    ·
                      refine ⟨239234744775068366507335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 318979659700091155343113 239234744775068366507335)
                      ·
                        rfl

theorem cell23_465908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_465908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465908 prefixEnd_465908 := by exact prefixLift 465908
  have htrace : WordTrace (prefixWord ++ tailWord_465908) baseStart_465908 baseEnd_465908 := by
    simpa [prefixWord, tailWord_465908, baseEnd_465908] using wordTrace_append hprefix tailTrace_465908
  have hstable : (prefixWord ++ tailWord_465908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465908).length < 2 ^ (prefixWord ++ tailWord_465908).sum := by decide
  have hdescent : baseEnd_465908 < baseStart_465908 := by decide
  rcases family_descends (prefixWord ++ tailWord_465908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465930 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_465930 : Nat := 118140960795 + 465930 * 2 ^ 59
def prefixEnd_465930 : Nat := 4983230072969 + 3 ^ 40 * 465930 * 2
def baseEnd_465930 : Nat := 239246041349467280432233

theorem tailTrace_465930 : CollatzResearch.WordTrace tailWord_465930 prefixEnd_465930 239246041349467280432233 := by
  unfold tailWord_465930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248465800505664838464811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11329242134681772902572829 4248465800505664838464811)
  ·
    refine ⟨6372698700758497257697217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248465800505664838464811 6372698700758497257697217)
    ·
      refine ⟨4779524025568872943272913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6372698700758497257697217 4779524025568872943272913)
      ·
        refine ⟨3584643019176654707454685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4779524025568872943272913 3584643019176654707454685)
        ·
          refine ⟨1344241132191245515295507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3584643019176654707454685 1344241132191245515295507)
          ·
            refine ⟨2016361698286868272943261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344241132191245515295507 2016361698286868272943261)
            ·
              refine ⟨756135636857575602353723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2016361698286868272943261 756135636857575602353723)
              ·
                refine ⟨1134203455286363403530585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756135636857575602353723 1134203455286363403530585)
                ·
                  refine ⟨850652591464772552647939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1134203455286363403530585 850652591464772552647939)
                  ·
                    refine ⟨1275978887197158828971909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 850652591464772552647939 1275978887197158828971909)
                    ·
                      refine ⟨239246041349467280432233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1275978887197158828971909 239246041349467280432233)
                      ·
                        rfl

theorem cell23_465930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_465930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465930 prefixEnd_465930 := by exact prefixLift 465930
  have htrace : WordTrace (prefixWord ++ tailWord_465930) baseStart_465930 baseEnd_465930 := by
    simpa [prefixWord, tailWord_465930, baseEnd_465930] using wordTrace_append hprefix tailTrace_465930
  have hstable : (prefixWord ++ tailWord_465930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465930).length < 2 ^ (prefixWord ++ tailWord_465930).sum := by decide
  have hdescent : baseEnd_465930 < baseStart_465930 := by decide
  rcases family_descends (prefixWord ++ tailWord_465930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465943 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_465943 : Nat := 118140960795 + 465943 * 2 ^ 59
def prefixEnd_465943 : Nat := 4983230072969 + 3 ^ 40 * 465943 * 2
def baseEnd_465943 : Nat := 239252716597975729569673

theorem tailTrace_465943 : CollatzResearch.WordTrace tailWord_465943 prefixEnd_465943 239252716597975729569673 := by
  unfold tailWord_465943
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994337350975562574082483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329558233983708382721655 16994337350975562574082483)
  ·
    refine ⟨25491506026463343861123725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16994337350975562574082483 25491506026463343861123725)
    ·
      refine ⟨9559314759923753947921397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25491506026463343861123725 9559314759923753947921397)
      ·
        refine ⟨896185758742851932617631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9559314759923753947921397 896185758742851932617631)
        ·
          refine ⟨1344278638114277898926447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896185758742851932617631 1344278638114277898926447)
          ·
            refine ⟨2016417957171416848389671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344278638114277898926447 2016417957171416848389671)
            ·
              refine ⟨3024626935757125272584507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016417957171416848389671 3024626935757125272584507)
              ·
                refine ⟨4536940403635687908876761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3024626935757125272584507 4536940403635687908876761)
                ·
                  refine ⟨3402705302726765931657571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4536940403635687908876761 3402705302726765931657571)
                  ·
                    refine ⟨5104057954090148897486357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3402705302726765931657571 5104057954090148897486357)
                    ·
                      refine ⟨239252716597975729569673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5104057954090148897486357 239252716597975729569673)
                      ·
                        rfl

theorem cell23_465943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_465943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465943 prefixEnd_465943 := by exact prefixLift 465943
  have htrace : WordTrace (prefixWord ++ tailWord_465943) baseStart_465943 baseEnd_465943 := by
    simpa [prefixWord, tailWord_465943, baseEnd_465943] using wordTrace_append hprefix tailTrace_465943
  have hstable : (prefixWord ++ tailWord_465943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465943).length < 2 ^ (prefixWord ++ tailWord_465943).sum := by decide
  have hdescent : baseEnd_465943 < baseStart_465943 := by decide
  rcases family_descends (prefixWord ++ tailWord_465943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465953 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 8]
def baseStart_465953 : Nat := 118140960795 + 465953 * 2 ^ 59
def prefixEnd_465953 : Nat := 4983230072969 + 3 ^ 40 * 465953 * 2
def baseEnd_465953 : Nat := 26584205711613410049403

theorem tailTrace_465953 : CollatzResearch.WordTrace tailWord_465953 prefixEnd_465953 26584205711613410049403 := by
  unfold tailWord_465953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994702080939334281946513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329801387292889521297675 16994702080939334281946513)
  ·
    refine ⟨12746026560704500711459885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16994702080939334281946513 12746026560704500711459885)
    ·
      refine ⟨4779759960264187766797457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12746026560704500711459885 4779759960264187766797457)
      ·
        refine ⟨3584819970198140825098093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4779759960264187766797457 3584819970198140825098093)
        ·
          refine ⟨1344307488824302809411785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3584819970198140825098093 1344307488824302809411785)
          ·
            refine ⟨1008230616618227107058839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344307488824302809411785 1008230616618227107058839)
            ·
              refine ⟨1512345924927340660588259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008230616618227107058839 1512345924927340660588259)
              ·
                refine ⟨2268518887391010990882389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1512345924927340660588259 2268518887391010990882389)
                ·
                  refine ⟨26584205711613410049403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2268518887391010990882389 26584205711613410049403)
                  ·
                    rfl

theorem cell23_465953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_465953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465953 prefixEnd_465953 := by exact prefixLift 465953
  have htrace : WordTrace (prefixWord ++ tailWord_465953) baseStart_465953 baseEnd_465953 := by
    simpa [prefixWord, tailWord_465953, baseEnd_465953] using wordTrace_append hprefix tailTrace_465953
  have hstable : (prefixWord ++ tailWord_465953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465953).length < 2 ^ (prefixWord ++ tailWord_465953).sum := by decide
  have hdescent : baseEnd_465953 < baseStart_465953 := by decide
  rcases family_descends (prefixWord ++ tailWord_465953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465970 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_465970 : Nat := 118140960795 + 465970 * 2 ^ 59
def prefixEnd_465970 : Nat := 4983230072969 + 3 ^ 40 * 465970 * 2
def baseEnd_465970 : Nat := 26585175619516347103561

theorem tailTrace_465970 : CollatzResearch.WordTrace tailWord_465970 prefixEnd_465970 26585175619516347103561 := by
  unfold tailWord_465970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248830530469436546328841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11330214747918497456876909 4248830530469436546328841)
  ·
    refine ⟨3186622897852077409746631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248830530469436546328841 3186622897852077409746631)
    ·
      refine ⟨4779934346778116114619947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186622897852077409746631 4779934346778116114619947)
      ·
        refine ⟨7169901520167174171929921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779934346778116114619947 7169901520167174171929921)
        ·
          refine ⟨5377426140125380628947441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7169901520167174171929921 5377426140125380628947441)
          ·
            refine ⟨4033069605094035471710581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377426140125380628947441 4033069605094035471710581)
            ·
              refine ⟨378100275477565825472867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4033069605094035471710581 378100275477565825472867)
              ·
                refine ⟨567150413216348738209301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378100275477565825472867 567150413216348738209301)
                ·
                  refine ⟨26585175619516347103561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 567150413216348738209301 26585175619516347103561)
                  ·
                    rfl

theorem cell23_465970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_465970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_465970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_465970 prefixEnd_465970 := by exact prefixLift 465970
  have htrace : WordTrace (prefixWord ++ tailWord_465970) baseStart_465970 baseEnd_465970 := by
    simpa [prefixWord, tailWord_465970, baseEnd_465970] using wordTrace_append hprefix tailTrace_465970
  have hstable : (prefixWord ++ tailWord_465970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465970).length < 2 ^ (prefixWord ++ tailWord_465970).sum := by decide
  have hdescent : baseEnd_465970 < baseStart_465970 := by decide
  rcases family_descends (prefixWord ++ tailWord_465970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466071 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_466071 : Nat := 118140960795 + 466071 * 2 ^ 59
def prefixEnd_466071 : Nat := 4983230072969 + 3 ^ 40 * 466071 * 2
def baseEnd_466071 : Nat := 239318442121751228769085

theorem tailTrace_466071 : CollatzResearch.WordTrace tailWord_466071 prefixEnd_466071 239318442121751228769085 := by
  unfold tailWord_466071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999005894511840434742067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11332670596341226956494711 16999005894511840434742067)
  ·
    refine ⟨25498508841767760652113101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16999005894511840434742067 25498508841767760652113101)
    ·
      refine ⟨9561940815662910244542413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25498508841767760652113101 9561940815662910244542413)
      ·
        refine ⟨3585727805873591341703405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9561940815662910244542413 3585727805873591341703405)
        ·
          refine ⟨1344647927202596753138777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3585727805873591341703405 1344647927202596753138777)
          ·
            refine ⟨1008485945401947564854083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344647927202596753138777 1008485945401947564854083)
            ·
              refine ⟨1512728918102921347281125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008485945401947564854083 1512728918102921347281125)
              ·
                refine ⟨283636672144297752615211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1512728918102921347281125 283636672144297752615211)
                ·
                  refine ⟨425455008216446628922817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283636672144297752615211 425455008216446628922817)
                  ·
                    refine ⟨319091256162334971692113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 425455008216446628922817 319091256162334971692113)
                    ·
                      refine ⟨239318442121751228769085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319091256162334971692113 239318442121751228769085)
                      ·
                        rfl

theorem cell23_466071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_466071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466071 prefixEnd_466071 := by exact prefixLift 466071
  have htrace : WordTrace (prefixWord ++ tailWord_466071) baseStart_466071 baseEnd_466071 := by
    simpa [prefixWord, tailWord_466071, baseEnd_466071] using wordTrace_append hprefix tailTrace_466071
  have hstable : (prefixWord ++ tailWord_466071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466071).length < 2 ^ (prefixWord ++ tailWord_466071).sum := by decide
  have hdescent : baseEnd_466071 < baseStart_466071 := by decide
  rcases family_descends (prefixWord ++ tailWord_466071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466087 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_466087 : Nat := 118140960795 + 466087 * 2 ^ 59
def prefixEnd_466087 : Nat := 4983230072969 + 3 ^ 40 * 466087 * 2
def baseEnd_466087 : Nat := 239326657812223166169011

theorem tailTrace_466087 : CollatzResearch.WordTrace tailWord_466087 prefixEnd_466087 239326657812223166169011 := by
  unfold tailWord_466087
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999589462453875167324515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11333059641635916778216343 16999589462453875167324515)
  ·
    refine ⟨25499384193680812750986773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16999589462453875167324515 25499384193680812750986773)
    ·
      refine ⟨1195283634078788097702505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25499384193680812750986773 1195283634078788097702505)
      ·
        refine ⟨896462725559091073276879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195283634078788097702505 896462725559091073276879)
        ·
          refine ⟨1344694088338636609915319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896462725559091073276879 1344694088338636609915319)
          ·
            refine ⟨2017041132507954914872979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344694088338636609915319 2017041132507954914872979)
            ·
              refine ⟨3025561698761932372309469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017041132507954914872979 3025561698761932372309469)
              ·
                refine ⟨1134585637035724639616051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3025561698761932372309469 1134585637035724639616051)
                ·
                  refine ⟨1701878455553586959424077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134585637035724639616051 1701878455553586959424077)
                  ·
                    refine ⟨638204420832595109784029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1701878455553586959424077 638204420832595109784029)
                    ·
                      refine ⟨239326657812223166169011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 638204420832595109784029 239326657812223166169011)
                      ·
                        rfl

theorem cell23_466087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_466087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466087 prefixEnd_466087 := by exact prefixLift 466087
  have htrace : WordTrace (prefixWord ++ tailWord_466087) baseStart_466087 baseEnd_466087 := by
    simpa [prefixWord, tailWord_466087, baseEnd_466087] using wordTrace_append hprefix tailTrace_466087
  have hstable : (prefixWord ++ tailWord_466087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466087).length < 2 ^ (prefixWord ++ tailWord_466087).sum := by decide
  have hdescent : baseEnd_466087 < baseStart_466087 := by decide
  rcases family_descends (prefixWord ++ tailWord_466087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466103 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 8]
def baseStart_466103 : Nat := 118140960795 + 466103 * 2 ^ 59
def prefixEnd_466103 : Nat := 4983230072969 + 3 ^ 40 * 466103 * 2
def baseEnd_466103 : Nat := 79778291167565034522979

theorem tailTrace_466103 : CollatzResearch.WordTrace tailWord_466103 prefixEnd_466103 79778291167565034522979 := by
  unfold tailWord_466103
  simp only [CollatzResearch.WordTrace]
  refine ⟨17000173030395909899906963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11333448686930606599937975 17000173030395909899906963)
  ·
    refine ⟨25500259545593864849860445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17000173030395909899906963 25500259545593864849860445)
    ·
      refine ⟨9562597329597699318697667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25500259545593864849860445 9562597329597699318697667)
      ·
        refine ⟨14343895994396548978046501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9562597329597699318697667 14343895994396548978046501)
        ·
          refine ⟨2689480498949352933383719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14343895994396548978046501 2689480498949352933383719)
          ·
            refine ⟨4034220748424029400075579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2689480498949352933383719 4034220748424029400075579)
            ·
              refine ⟨6051331122636044100113369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034220748424029400075579 6051331122636044100113369)
              ·
                refine ⟨4538498341977033075085027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6051331122636044100113369 4538498341977033075085027)
                ·
                  refine ⟨6807747512965549612627541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4538498341977033075085027 6807747512965549612627541)
                  ·
                    refine ⟨79778291167565034522979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6807747512965549612627541 79778291167565034522979)
                    ·
                      rfl

theorem cell23_466103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_466103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466103 prefixEnd_466103 := by exact prefixLift 466103
  have htrace : WordTrace (prefixWord ++ tailWord_466103) baseStart_466103 baseEnd_466103 := by
    simpa [prefixWord, tailWord_466103, baseEnd_466103] using wordTrace_append hprefix tailTrace_466103
  have hstable : (prefixWord ++ tailWord_466103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466103).length < 2 ^ (prefixWord ++ tailWord_466103).sum := by decide
  have hdescent : baseEnd_466103 < baseStart_466103 := by decide
  rcases family_descends (prefixWord ++ tailWord_466103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466144 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2]
def baseStart_466144 : Nat := 118140960795 + 466144 * 2 ^ 59
def prefixEnd_466144 : Nat := 4983230072969 + 3 ^ 40 * 466144 * 2
def baseEnd_466144 : Nat := 239355926209529443156249

theorem tailTrace_466144 : CollatzResearch.WordTrace tailWord_466144 prefixEnd_466144 239355926209529443156249 := by
  unfold tailWord_466144
  simp only [CollatzResearch.WordTrace]
  refine ⟨8500834211623686951074743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11334445615498249268099657 8500834211623686951074743)
  ·
    refine ⟨12751251317435530426612115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8500834211623686951074743 12751251317435530426612115)
    ·
      refine ⟨19126876976153295639918173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12751251317435530426612115 19126876976153295639918173)
      ·
        refine ⟨7172578866057485864969315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19126876976153295639918173 7172578866057485864969315)
        ·
          refine ⟨10758868299086228797453973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172578866057485864969315 10758868299086228797453973)
          ·
            refine ⟨504321951519666974880655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10758868299086228797453973 504321951519666974880655)
            ·
              refine ⟨756482927279500462320983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504321951519666974880655 756482927279500462320983)
              ·
                refine ⟨1134724390919250693481475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756482927279500462320983 1134724390919250693481475)
                ·
                  refine ⟨1702086586378876040222213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134724390919250693481475 1702086586378876040222213)
                  ·
                    refine ⟨319141234946039257541665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1702086586378876040222213 319141234946039257541665)
                    ·
                      refine ⟨239355926209529443156249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319141234946039257541665 239355926209529443156249)
                      ·
                        rfl

theorem cell23_466144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_466144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466144 prefixEnd_466144 := by exact prefixLift 466144
  have htrace : WordTrace (prefixWord ++ tailWord_466144) baseStart_466144 baseEnd_466144 := by
    simpa [prefixWord, tailWord_466144, baseEnd_466144] using wordTrace_append hprefix tailTrace_466144
  have hstable : (prefixWord ++ tailWord_466144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466144).length < 2 ^ (prefixWord ++ tailWord_466144).sum := by decide
  have hdescent : baseEnd_466144 < baseStart_466144 := by decide
  rcases family_descends (prefixWord ++ tailWord_466144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466184 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 7]
def baseStart_466184 : Nat := 118140960795 + 466184 * 2 ^ 59
def prefixEnd_466184 : Nat := 4983230072969 + 3 ^ 40 * 466184 * 2
def baseEnd_466184 : Nat := 26597385048412142961785

theorem tailTrace_466184 : CollatzResearch.WordTrace tailWord_466184 prefixEnd_466184 26597385048412142961785 := by
  unfold tailWord_466184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501563671551230366802803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11335418228734973822403737 8501563671551230366802803)
  ·
    refine ⟨12752345507326845550204205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501563671551230366802803 12752345507326845550204205)
    ·
      refine ⟨4782129565247567081326577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12752345507326845550204205 4782129565247567081326577)
      ·
        refine ⟨3586597173935675310994933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782129565247567081326577 3586597173935675310994933)
        ·
          refine ⟨336243485056469560405775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3586597173935675310994933 336243485056469560405775)
          ·
            refine ⟨504365227584704340608663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336243485056469560405775 504365227584704340608663)
            ·
              refine ⟨756547841377056510912995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504365227584704340608663 756547841377056510912995)
              ·
                refine ⟨1134821762065584766369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756547841377056510912995 1134821762065584766369493)
                ·
                  refine ⟨26597385048412142961785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1134821762065584766369493 26597385048412142961785)
                  ·
                    rfl

theorem cell23_466184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_466184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466184 prefixEnd_466184 := by exact prefixLift 466184
  have htrace : WordTrace (prefixWord ++ tailWord_466184) baseStart_466184 baseEnd_466184 := by
    simpa [prefixWord, tailWord_466184, baseEnd_466184] using wordTrace_append hprefix tailTrace_466184
  have hstable : (prefixWord ++ tailWord_466184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466184).length < 2 ^ (prefixWord ++ tailWord_466184).sum := by decide
  have hdescent : baseEnd_466184 < baseStart_466184 := by decide
  rcases family_descends (prefixWord ++ tailWord_466184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466190 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_466190 : Nat := 118140960795 + 466190 * 2 ^ 59
def prefixEnd_466190 : Nat := 4983230072969 + 3 ^ 40 * 466190 * 2
def baseEnd_466190 : Nat := 239379546319636263181037

theorem tailTrace_466190 : CollatzResearch.WordTrace tailWord_466190 prefixEnd_466190 239379546319636263181037 := by
  unfold tailWord_466190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125418272635090469790503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11335564120720482505549349 2125418272635090469790503)
  ·
    refine ⟨3188127408952635704685755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2125418272635090469790503 3188127408952635704685755)
    ·
      refine ⟨4782191113428953557028633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188127408952635704685755 4782191113428953557028633)
      ·
        refine ⟨3586643335071715167771475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4782191113428953557028633 3586643335071715167771475)
        ·
          refine ⟨5379965002607572751657213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586643335071715167771475 5379965002607572751657213)
          ·
            refine ⟨2017486875977839781871455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5379965002607572751657213 2017486875977839781871455)
            ·
              refine ⟨3026230313966759672807183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017486875977839781871455 3026230313966759672807183)
              ·
                refine ⟨4539345470950139509210775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026230313966759672807183 4539345470950139509210775)
                ·
                  refine ⟨6809018206425209263816163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4539345470950139509210775 6809018206425209263816163)
                  ·
                    refine ⟨10213527309637813895724245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6809018206425209263816163 10213527309637813895724245)
                    ·
                      refine ⟨239379546319636263181037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10213527309637813895724245 239379546319636263181037)
                      ·
                        rfl

theorem cell23_466190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_466190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466190 prefixEnd_466190 := by exact prefixLift 466190
  have htrace : WordTrace (prefixWord ++ tailWord_466190) baseStart_466190 baseEnd_466190 := by
    simpa [prefixWord, tailWord_466190, baseEnd_466190] using wordTrace_append hprefix tailTrace_466190
  have hstable : (prefixWord ++ tailWord_466190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466190).length < 2 ^ (prefixWord ++ tailWord_466190).sum := by decide
  have hdescent : baseEnd_466190 < baseStart_466190 := by decide
  rcases family_descends (prefixWord ++ tailWord_466190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466287 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 1, 5]
def baseStart_466287 : Nat := 118140960795 + 466287 * 2 ^ 59
def prefixEnd_466287 : Nat := 4983230072969 + 3 ^ 40 * 466287 * 2
def baseEnd_466287 : Nat := 79809784647707461222697

theorem tailTrace_466287 : CollatzResearch.WordTrace tailWord_466287 prefixEnd_466287 79809784647707461222697 := by
  unfold tailWord_466287
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006884061729309324605115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11337922707819539549736743 17006884061729309324605115)
  ·
    refine ⟨25510326092593963986907673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17006884061729309324605115 25510326092593963986907673)
    ·
      refine ⟨19132744569445472990180755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25510326092593963986907673 19132744569445472990180755)
      ·
        refine ⟨28699116854168209485271133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19132744569445472990180755 28699116854168209485271133)
        ·
          refine ⟨10762168820313078556976675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28699116854168209485271133 10762168820313078556976675)
          ·
            refine ⟨16143253230469617835465013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762168820313078556976675 16143253230469617835465013)
            ·
              refine ⟨1513429990356526672074845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16143253230469617835465013 1513429990356526672074845)
              ·
                refine ⟨567536246383697502028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1513429990356526672074845 567536246383697502028067)
                ·
                  refine ⟨851304369575546253042101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567536246383697502028067 851304369575546253042101)
                  ·
                    refine ⟨79809784647707461222697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 851304369575546253042101 79809784647707461222697)
                    ·
                      rfl

theorem cell23_466287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_466287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466287 prefixEnd_466287 := by exact prefixLift 466287
  have htrace : WordTrace (prefixWord ++ tailWord_466287) baseStart_466287 baseEnd_466287 := by
    simpa [prefixWord, tailWord_466287, baseEnd_466287] using wordTrace_append hprefix tailTrace_466287
  have hstable : (prefixWord ++ tailWord_466287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466287).length < 2 ^ (prefixWord ++ tailWord_466287).sum := by decide
  have hdescent : baseEnd_466287 < baseStart_466287 := by decide
  rcases family_descends (prefixWord ++ tailWord_466287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466301 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_466301 : Nat := 118140960795 + 466301 * 2 ^ 59
def prefixEnd_466301 : Nat := 4983230072969 + 3 ^ 40 * 466301 * 2
def baseEnd_466301 : Nat := 239436542672285328893027

theorem tailTrace_466301 : CollatzResearch.WordTrace tailWord_466301 prefixEnd_466301 239436542672285328893027 := by
  unfold tailWord_466301
  simp only [CollatzResearch.WordTrace]
  refine ⟨17007394683678589715614757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11338263122452393143743171 17007394683678589715614757)
  ·
    refine ⟨3188886503189735571677767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17007394683678589715614757 3188886503189735571677767)
    ·
      refine ⟨4783329754784603357516651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188886503189735571677767 4783329754784603357516651)
      ·
        refine ⟨7174994632176905036274977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783329754784603357516651 7174994632176905036274977)
        ·
          refine ⟨5381245974132678777206233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7174994632176905036274977 5381245974132678777206233)
          ·
            refine ⟨4035934480599509082904675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381245974132678777206233 4035934480599509082904675)
            ·
              refine ⟨6053901720899263624357013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4035934480599509082904675 6053901720899263624357013)
              ·
                refine ⟨283776643167152982391735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6053901720899263624357013 283776643167152982391735)
                ·
                  refine ⟨425664964750729473587603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283776643167152982391735 425664964750729473587603)
                  ·
                    refine ⟨638497447126094210381405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 425664964750729473587603 638497447126094210381405)
                    ·
                      refine ⟨239436542672285328893027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 638497447126094210381405 239436542672285328893027)
                      ·
                        rfl

theorem cell23_466301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_466301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466301 prefixEnd_466301 := by exact prefixLift 466301
  have htrace : WordTrace (prefixWord ++ tailWord_466301) baseStart_466301 baseEnd_466301 := by
    simpa [prefixWord, tailWord_466301, baseEnd_466301] using wordTrace_append hprefix tailTrace_466301
  have hstable : (prefixWord ++ tailWord_466301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466301).length < 2 ^ (prefixWord ++ tailWord_466301).sum := by decide
  have hdescent : baseEnd_466301 < baseStart_466301 := by decide
  rcases family_descends (prefixWord ++ tailWord_466301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466364 : List Nat := [2, 2, 2, 4, 2, 1, 2, 8]
def baseStart_466364 : Nat := 118140960795 + 466364 * 2 ^ 59
def prefixEnd_466364 : Nat := 4983230072969 + 3 ^ 40 * 466364 * 2
def baseEnd_466364 : Nat := 8869218220500688237231

theorem tailTrace_466364 : CollatzResearch.WordTrace tailWord_466364 prefixEnd_466364 8869218220500688237231 := by
  unfold tailWord_466364
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504846241225175737579073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11339794988300234316772097 8504846241225175737579073)
  ·
    refine ⟨6378634680918881803184305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8504846241225175737579073 6378634680918881803184305)
    ·
      refine ⟨4783976010689161352388229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6378634680918881803184305 4783976010689161352388229)
      ·
        refine ⟨896995502004217753572793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4783976010689161352388229 896995502004217753572793)
        ·
          refine ⟨672746626503163315179595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896995502004217753572793 672746626503163315179595)
          ·
            refine ⟨1009119939754744972769393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672746626503163315179595 1009119939754744972769393)
            ·
              refine ⟨756839954816058729577045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009119939754744972769393 756839954816058729577045)
              ·
                refine ⟨8869218220500688237231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 756839954816058729577045 8869218220500688237231)
                ·
                  rfl

theorem cell23_466364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 8].length) (baseStart_466364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466364 prefixEnd_466364 := by exact prefixLift 466364
  have htrace : WordTrace (prefixWord ++ tailWord_466364) baseStart_466364 baseEnd_466364 := by
    simpa [prefixWord, tailWord_466364, baseEnd_466364] using wordTrace_append hprefix tailTrace_466364
  have hstable : (prefixWord ++ tailWord_466364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466364).length < 2 ^ (prefixWord ++ tailWord_466364).sum := by decide
  have hdescent : baseEnd_466364 < baseStart_466364 := by decide
  rcases family_descends (prefixWord ++ tailWord_466364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2]
def baseStart_466384 : Nat := 118140960795 + 466384 * 2 ^ 59
def prefixEnd_466384 : Nat := 4983230072969 + 3 ^ 40 * 466384 * 2
def baseEnd_466384 : Nat := 239479161566608504155145

theorem tailTrace_466384 : CollatzResearch.WordTrace tailWord_466384 prefixEnd_466384 239479161566608504155145 := by
  unfold tailWord_466384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505210971188947445443103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11340281294918596593924137 8505210971188947445443103)
  ·
    refine ⟨12757816456783421168164655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505210971188947445443103 12757816456783421168164655)
    ·
      refine ⟨19136724685175131752246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757816456783421168164655 19136724685175131752246983)
      ·
        refine ⟨28705087027762697628370475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19136724685175131752246983 28705087027762697628370475)
        ·
          refine ⟨43057630541644046442555713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28705087027762697628370475 43057630541644046442555713)
          ·
            refine ⟨32293222906233034831916785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43057630541644046442555713 32293222906233034831916785)
            ·
              refine ⟨24219917179674776123937589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32293222906233034831916785 24219917179674776123937589)
              ·
                refine ⟨2270617235594510261619149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24219917179674776123937589 2270617235594510261619149)
                ·
                  refine ⟨851481463347941348107181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2270617235594510261619149 851481463347941348107181)
                  ·
                    refine ⟨319305548755478005540193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851481463347941348107181 319305548755478005540193)
                    ·
                      refine ⟨239479161566608504155145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319305548755478005540193 239479161566608504155145)
                      ·
                        rfl

theorem cell23_466384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2].length) (baseStart_466384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466384 prefixEnd_466384 := by exact prefixLift 466384
  have htrace : WordTrace (prefixWord ++ tailWord_466384) baseStart_466384 baseEnd_466384 := by
    simpa [prefixWord, tailWord_466384, baseEnd_466384] using wordTrace_append hprefix tailTrace_466384
  have hstable : (prefixWord ++ tailWord_466384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466384).length < 2 ^ (prefixWord ++ tailWord_466384).sum := by decide
  have hdescent : baseEnd_466384 < baseStart_466384 := by decide
  rcases family_descends (prefixWord ++ tailWord_466384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466427 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4]
def baseStart_466427 : Nat := 118140960795 + 466427 * 2 ^ 59
def prefixEnd_466427 : Nat := 4983230072969 + 3 ^ 40 * 466427 * 2
def baseEnd_466427 : Nat := 239501241234751835917447

theorem tailTrace_466427 : CollatzResearch.WordTrace tailWord_466427 prefixEnd_466427 239501241234751835917447 := by
  unfold tailWord_466427
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011990281222113234701535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11341326854148075489801023 17011990281222113234701535)
  ·
    refine ⟨25517985421833169852052303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17011990281222113234701535 25517985421833169852052303)
    ·
      refine ⟨38276978132749754778078455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25517985421833169852052303 38276978132749754778078455)
      ·
        refine ⟨57415467199124632167117683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38276978132749754778078455 57415467199124632167117683)
        ·
          refine ⟨86123200798686948250676525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57415467199124632167117683 86123200798686948250676525)
          ·
            refine ⟨32296200299507605594003697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86123200798686948250676525 32296200299507605594003697)
            ·
              refine ⟨24222150224630704195502773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32296200299507605594003697 24222150224630704195502773)
              ·
                refine ⟨2270826583559128518328385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24222150224630704195502773 2270826583559128518328385)
                ·
                  refine ⟨1703119937669346388746289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2270826583559128518328385 1703119937669346388746289)
                  ·
                    refine ⟨1277339953252009791559717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1703119937669346388746289 1277339953252009791559717)
                    ·
                      refine ⟨239501241234751835917447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1277339953252009791559717 239501241234751835917447)
                      ·
                        rfl

theorem cell23_466427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_466427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466427 prefixEnd_466427 := by exact prefixLift 466427
  have htrace : WordTrace (prefixWord ++ tailWord_466427) baseStart_466427 baseEnd_466427 := by
    simpa [prefixWord, tailWord_466427, baseEnd_466427] using wordTrace_append hprefix tailTrace_466427
  have hstable : (prefixWord ++ tailWord_466427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466427).length < 2 ^ (prefixWord ++ tailWord_466427).sum := by decide
  have hdescent : baseEnd_466427 < baseStart_466427 := by decide
  rcases family_descends (prefixWord ++ tailWord_466427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466465 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_466465 : Nat := 118140960795 + 466465 * 2 ^ 59
def prefixEnd_466465 : Nat := 4983230072969 + 3 ^ 40 * 466465 * 2
def baseEnd_466465 : Nat := 239520753499622687242273

theorem tailTrace_466465 : CollatzResearch.WordTrace tailWord_466465 prefixEnd_466465 239520753499622687242273 := by
  unfold tailWord_466465
  simp only [CollatzResearch.WordTrace]
  refine ⟨17013376255084445724584849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11342250836722963816389899 17013376255084445724584849)
  ·
    refine ⟨12760032191313334293438637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17013376255084445724584849 12760032191313334293438637)
    ·
      refine ⟨4785012071742500360039489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12760032191313334293438637 4785012071742500360039489)
      ·
        refine ⟨3588759053806875270029617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785012071742500360039489 3588759053806875270029617)
        ·
          refine ⟨2691569290355156452522213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588759053806875270029617 2691569290355156452522213)
          ·
            refine ⟨504669241941591834847915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2691569290355156452522213 504669241941591834847915)
            ·
              refine ⟨757003862912387752271873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504669241941591834847915 757003862912387752271873)
              ·
                refine ⟨567752897184290814203905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757003862912387752271873 567752897184290814203905)
                ·
                  refine ⟨425814672888218110652929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567752897184290814203905 425814672888218110652929)
                  ·
                    refine ⟨319361004666163582989697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 425814672888218110652929 319361004666163582989697)
                    ·
                      refine ⟨239520753499622687242273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319361004666163582989697 239520753499622687242273)
                      ·
                        rfl

theorem cell23_466465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_466465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466465 prefixEnd_466465 := by exact prefixLift 466465
  have htrace : WordTrace (prefixWord ++ tailWord_466465) baseStart_466465 baseEnd_466465 := by
    simpa [prefixWord, tailWord_466465, baseEnd_466465] using wordTrace_append hprefix tailTrace_466465
  have hstable : (prefixWord ++ tailWord_466465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466465).length < 2 ^ (prefixWord ++ tailWord_466465).sum := by decide
  have hdescent : baseEnd_466465 < baseStart_466465 := by decide
  rcases family_descends (prefixWord ++ tailWord_466465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466507 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_466507 : Nat := 118140960795 + 466507 * 2 ^ 59
def prefixEnd_466507 : Nat := 4983230072969 + 3 ^ 40 * 466507 * 2
def baseEnd_466507 : Nat := 239542319687111522917079

theorem tailTrace_466507 : CollatzResearch.WordTrace tailWord_466507 prefixEnd_466507 239542319687111522917079 := by
  unfold tailWord_466507
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014908120932286897613775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11343272080621524598409183 17014908120932286897613775)
  ·
    refine ⟨25522362181398430346420663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17014908120932286897613775 25522362181398430346420663)
    ·
      refine ⟨38283543272097645519630995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25522362181398430346420663 38283543272097645519630995)
      ·
        refine ⟨57425314908146468279446493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38283543272097645519630995 57425314908146468279446493)
        ·
          refine ⟨21534493090554925604792435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57425314908146468279446493 21534493090554925604792435)
          ·
            refine ⟨32301739635832388407188653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534493090554925604792435 32301739635832388407188653)
            ·
              refine ⟨12113152363437145652695745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32301739635832388407188653 12113152363437145652695745)
              ·
                refine ⟨9084864272577859239521809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12113152363437145652695745 9084864272577859239521809)
                ·
                  refine ⟨6813648204433394429641357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9084864272577859239521809 6813648204433394429641357)
                  ·
                    refine ⟨2555118076662522911115509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6813648204433394429641357 2555118076662522911115509)
                    ·
                      refine ⟨239542319687111522917079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2555118076662522911115509 239542319687111522917079)
                      ·
                        rfl

theorem cell23_466507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_466507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466507 prefixEnd_466507 := by exact prefixLift 466507
  have htrace : WordTrace (prefixWord ++ tailWord_466507) baseStart_466507 baseEnd_466507 := by
    simpa [prefixWord, tailWord_466507, baseEnd_466507] using wordTrace_append hprefix tailTrace_466507
  have hstable : (prefixWord ++ tailWord_466507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466507).length < 2 ^ (prefixWord ++ tailWord_466507).sum := by decide
  have hdescent : baseEnd_466507 < baseStart_466507 := by decide
  rcases family_descends (prefixWord ++ tailWord_466507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466531 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 3, 4]
def baseStart_466531 : Nat := 118140960795 + 466531 * 2 ^ 59
def prefixEnd_466531 : Nat := 4983230072969 + 3 ^ 40 * 466531 * 2
def baseEnd_466531 : Nat := 79851547740939809672323

theorem tailTrace_466531 : CollatzResearch.WordTrace tailWord_466531 prefixEnd_466531 79851547740939809672323 := by
  unfold tailWord_466531
  simp only [CollatzResearch.WordTrace]
  refine ⟨17015783472845338996487447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11343855648563559330991631 17015783472845338996487447)
  ·
    refine ⟨25523675209268008494731171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17015783472845338996487447 25523675209268008494731171)
    ·
      refine ⟨38285512813902012742096757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25523675209268008494731171 38285512813902012742096757)
      ·
        refine ⟨3589266826303313694571571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38285512813902012742096757 3589266826303313694571571)
        ·
          refine ⟨5383900239454970541857357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589266826303313694571571 5383900239454970541857357)
          ·
            refine ⟨2018962589795613953196509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5383900239454970541857357 2018962589795613953196509)
            ·
              refine ⟨757110971173355232448691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018962589795613953196509 757110971173355232448691)
              ·
                refine ⟨1135666456760032848673037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757110971173355232448691 1135666456760032848673037)
                ·
                  refine ⟨425874921285012318252389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135666456760032848673037 425874921285012318252389)
                  ·
                    refine ⟨79851547740939809672323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425874921285012318252389 79851547740939809672323)
                    ·
                      rfl

theorem cell23_466531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 4].length) (baseStart_466531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466531 prefixEnd_466531 := by exact prefixLift 466531
  have htrace : WordTrace (prefixWord ++ tailWord_466531) baseStart_466531 baseEnd_466531 := by
    simpa [prefixWord, tailWord_466531, baseEnd_466531] using wordTrace_append hprefix tailTrace_466531
  have hstable : (prefixWord ++ tailWord_466531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466531).length < 2 ^ (prefixWord ++ tailWord_466531).sum := by decide
  have hdescent : baseEnd_466531 < baseStart_466531 := by decide
  rcases family_descends (prefixWord ++ tailWord_466531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466547 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_466547 : Nat := 118140960795 + 466547 * 2 ^ 59
def prefixEnd_466547 : Nat := 4983230072969 + 3 ^ 40 * 466547 * 2
def baseEnd_466547 : Nat := 239562858913291366416895

theorem tailTrace_466547 : CollatzResearch.WordTrace tailWord_466547 prefixEnd_466547 239562858913291366416895 := by
  unfold tailWord_466547
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016367040787373729069895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11344244693858249152713263 17016367040787373729069895)
  ·
    refine ⟨25524550561181060593604843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016367040787373729069895 25524550561181060593604843)
    ·
      refine ⟨38286825841771590890407265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25524550561181060593604843 38286825841771590890407265)
      ·
        refine ⟨28715119381328693167805449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38286825841771590890407265 28715119381328693167805449)
        ·
          refine ⟨21536339535996519875854087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28715119381328693167805449 21536339535996519875854087)
          ·
            refine ⟨32304509303994779813781131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21536339535996519875854087 32304509303994779813781131)
            ·
              refine ⟨48456763955992169720671697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32304509303994779813781131 48456763955992169720671697)
              ·
                refine ⟨36342572966994127290503773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48456763955992169720671697 36342572966994127290503773)
                ·
                  refine ⟨13628464862622797733938915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36342572966994127290503773 13628464862622797733938915)
                  ·
                    refine ⟨20442697293934196600908373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13628464862622797733938915 20442697293934196600908373)
                    ·
                      refine ⟨239562858913291366416895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 20442697293934196600908373 239562858913291366416895)
                      ·
                        rfl

theorem cell23_466547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_466547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466547 prefixEnd_466547 := by exact prefixLift 466547
  have htrace : WordTrace (prefixWord ++ tailWord_466547) baseStart_466547 baseEnd_466547 := by
    simpa [prefixWord, tailWord_466547, baseEnd_466547] using wordTrace_append hprefix tailTrace_466547
  have hstable : (prefixWord ++ tailWord_466547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466547).length < 2 ^ (prefixWord ++ tailWord_466547).sum := by decide
  have hdescent : baseEnd_466547 < baseStart_466547 := by decide
  rcases family_descends (prefixWord ++ tailWord_466547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466578 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_466578 : Nat := 118140960795 + 466578 * 2 ^ 59
def prefixEnd_466578 : Nat := 4983230072969 + 3 ^ 40 * 466578 * 2
def baseEnd_466578 : Nat := 26619864090397860569917

theorem tailTrace_466578 : CollatzResearch.WordTrace tailWord_466578 prefixEnd_466578 26619864090397860569917 := by
  unfold tailWord_466578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254374425918766505862097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11344998469116710682298925 4254374425918766505862097)
  ·
    refine ⟨3190780819439074879396573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4254374425918766505862097 3190780819439074879396573)
    ·
      refine ⟨1196542807289653079773715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3190780819439074879396573 1196542807289653079773715)
      ·
        refine ⟨1794814210934479619660573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196542807289653079773715 1794814210934479619660573)
        ·
          refine ⟨673055329100429857372715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1794814210934479619660573 673055329100429857372715)
          ·
            refine ⟨1009582993650644786059073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673055329100429857372715 1009582993650644786059073)
            ·
              refine ⟨757187245237983589544305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009582993650644786059073 757187245237983589544305)
              ·
                refine ⟨567890433928487692158229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757187245237983589544305 567890433928487692158229)
                ·
                  refine ⟨26619864090397860569917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 567890433928487692158229 26619864090397860569917)
                  ·
                    rfl

theorem cell23_466578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_466578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466578 prefixEnd_466578 := by exact prefixLift 466578
  have htrace : WordTrace (prefixWord ++ tailWord_466578) baseStart_466578 baseEnd_466578 := by
    simpa [prefixWord, tailWord_466578, baseEnd_466578] using wordTrace_append hprefix tailTrace_466578
  have hstable : (prefixWord ++ tailWord_466578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466578).length < 2 ^ (prefixWord ++ tailWord_466578).sum := by decide
  have hdescent : baseEnd_466578 < baseStart_466578 := by decide
  rcases family_descends (prefixWord ++ tailWord_466578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466611 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 4]
def baseStart_466611 : Nat := 118140960795 + 466611 * 2 ^ 59
def prefixEnd_466611 : Nat := 4983230072969 + 3 ^ 40 * 466611 * 2
def baseEnd_466611 : Nat := 239595721675179116016601

theorem tailTrace_466611 : CollatzResearch.WordTrace tailWord_466611 prefixEnd_466611 239595721675179116016601 := by
  unfold tailWord_466611
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018701312555512659399687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345800875037008439599791 17018701312555512659399687)
  ·
    refine ⟨25528051968833268989099531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17018701312555512659399687 25528051968833268989099531)
    ·
      refine ⟨38292077953249903483649297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25528051968833268989099531 38292077953249903483649297)
      ·
        refine ⟨28719058464937427612736973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38292077953249903483649297 28719058464937427612736973)
        ·
          refine ⟨10769646924351535354776365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28719058464937427612736973 10769646924351535354776365)
          ·
            refine ⟨4038617596631825758041137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10769646924351535354776365 4038617596631825758041137)
            ·
              refine ⟨3028963197473869318530853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038617596631825758041137 3028963197473869318530853)
              ·
                refine ⟨567930599526350497224535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3028963197473869318530853 567930599526350497224535)
                ·
                  refine ⟨851895899289525745836803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567930599526350497224535 851895899289525745836803)
                  ·
                    refine ⟨1277843848934288618755205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851895899289525745836803 1277843848934288618755205)
                    ·
                      refine ⟨239595721675179116016601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1277843848934288618755205 239595721675179116016601)
                      ·
                        rfl

theorem cell23_466611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_466611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466611 prefixEnd_466611 := by exact prefixLift 466611
  have htrace : WordTrace (prefixWord ++ tailWord_466611) baseStart_466611 baseEnd_466611 := by
    simpa [prefixWord, tailWord_466611, baseEnd_466611] using wordTrace_append hprefix tailTrace_466611
  have hstable : (prefixWord ++ tailWord_466611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466611).length < 2 ^ (prefixWord ++ tailWord_466611).sum := by decide
  have hdescent : baseEnd_466611 < baseStart_466611 := by decide
  rcases family_descends (prefixWord ++ tailWord_466611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466615 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_466615 : Nat := 118140960795 + 466615 * 2 ^ 59
def prefixEnd_466615 : Nat := 4983230072969 + 3 ^ 40 * 466615 * 2
def baseEnd_466615 : Nat := 239597775597797100366583

theorem tailTrace_466615 : CollatzResearch.WordTrace tailWord_466615 prefixEnd_466615 239597775597797100366583 := by
  unfold tailWord_466615
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018847204541021342545299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345898136360680895030199 17018847204541021342545299)
  ·
    refine ⟨25528270806811532013817949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17018847204541021342545299 25528270806811532013817949)
    ·
      refine ⟨9573101552554324505181731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25528270806811532013817949 9573101552554324505181731)
      ·
        refine ⟨14359652328831486757772597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573101552554324505181731 14359652328831486757772597)
        ·
          refine ⟨1346217405827951883541181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14359652328831486757772597 1346217405827951883541181)
          ·
            refine ⟨504831527185481956327943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1346217405827951883541181 504831527185481956327943)
            ·
              refine ⟨757247290778222934491915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504831527185481956327943 757247290778222934491915)
              ·
                refine ⟨1135870936167334401737873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757247290778222934491915 1135870936167334401737873)
                ·
                  refine ⟨851903202125500801303405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1135870936167334401737873 851903202125500801303405)
                  ·
                    refine ⟨319463700797062800488777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 851903202125500801303405 319463700797062800488777)
                    ·
                      refine ⟨239597775597797100366583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319463700797062800488777 239597775597797100366583)
                      ·
                        rfl

theorem cell23_466615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_466615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466615 prefixEnd_466615 := by exact prefixLift 466615
  have htrace : WordTrace (prefixWord ++ tailWord_466615) baseStart_466615 baseEnd_466615 := by
    simpa [prefixWord, tailWord_466615, baseEnd_466615] using wordTrace_append hprefix tailTrace_466615
  have hstable : (prefixWord ++ tailWord_466615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466615).length < 2 ^ (prefixWord ++ tailWord_466615).sum := by decide
  have hdescent : baseEnd_466615 < baseStart_466615 := by decide
  rcases family_descends (prefixWord ++ tailWord_466615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466621 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_466621 : Nat := 118140960795 + 466621 * 2 ^ 59
def prefixEnd_466621 : Nat := 4983230072969 + 3 ^ 40 * 466621 * 2
def baseEnd_466621 : Nat := 79866952160574692297185

theorem tailTrace_466621 : CollatzResearch.WordTrace tailWord_466621 prefixEnd_466621 79866952160574692297185 := by
  unfold tailWord_466621
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019066042519284367263717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11346044028346189578175811 17019066042519284367263717)
  ·
    refine ⟨3191074882972365818861947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17019066042519284367263717 3191074882972365818861947)
    ·
      refine ⟨4786612324458548728292921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191074882972365818861947 4786612324458548728292921)
      ·
        refine ⟨3589959243343911546219691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4786612324458548728292921 3589959243343911546219691)
        ·
          refine ⟨5384938865015867319329537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589959243343911546219691 5384938865015867319329537)
          ·
            refine ⟨4038704148761900489497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384938865015867319329537 4038704148761900489497153)
            ·
              refine ⟨3029028111571425367122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038704148761900489497153 3029028111571425367122865)
              ·
                refine ⟨2271771083678569025342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029028111571425367122865 2271771083678569025342149)
                ·
                  refine ⟨425957078189731692251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271771083678569025342149 425957078189731692251653)
                  ·
                    refine ⟨79866952160574692297185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425957078189731692251653 79866952160574692297185)
                    ·
                      rfl

theorem cell23_466621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_466621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466621 prefixEnd_466621 := by exact prefixLift 466621
  have htrace : WordTrace (prefixWord ++ tailWord_466621) baseStart_466621 baseEnd_466621 := by
    simpa [prefixWord, tailWord_466621, baseEnd_466621] using wordTrace_append hprefix tailTrace_466621
  have hstable : (prefixWord ++ tailWord_466621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466621).length < 2 ^ (prefixWord ++ tailWord_466621).sum := by decide
  have hdescent : baseEnd_466621 < baseStart_466621 := by decide
  rcases family_descends (prefixWord ++ tailWord_466621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466622 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_466622 : Nat := 118140960795 + 466622 * 2 ^ 59
def prefixEnd_466622 : Nat := 4983230072969 + 3 ^ 40 * 466622 * 2
def baseEnd_466622 : Nat := 239601369962378572979051

theorem tailTrace_466622 : CollatzResearch.WordTrace tailWord_466622 prefixEnd_466622 239601369962378572979051 := by
  unfold tailWord_466622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127387814439457692256265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11346068343677107692033413 2127387814439457692256265)
  ·
    refine ⟨1595540860829593269192199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127387814439457692256265 1595540860829593269192199)
    ·
      refine ⟨2393311291244389903788299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595540860829593269192199 2393311291244389903788299)
      ·
        refine ⟨3589966936866584855682449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393311291244389903788299 3589966936866584855682449)
        ·
          refine ⟨2692475202649938641761837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589966936866584855682449 2692475202649938641761837)
          ·
            refine ⟨1009678200993726990660689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2692475202649938641761837 1009678200993726990660689)
            ·
              refine ⟨757258650745295242995517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009678200993726990660689 757258650745295242995517)
              ·
                refine ⟨283971994029485716123319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757258650745295242995517 283971994029485716123319)
                ·
                  refine ⟨425957991044228574184979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283971994029485716123319 425957991044228574184979)
                  ·
                    refine ⟨638936986566342861277469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 425957991044228574184979 638936986566342861277469)
                    ·
                      refine ⟨239601369962378572979051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 638936986566342861277469 239601369962378572979051)
                      ·
                        rfl

theorem cell23_466622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_466622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466622 prefixEnd_466622 := by exact prefixLift 466622
  have htrace : WordTrace (prefixWord ++ tailWord_466622) baseStart_466622 baseEnd_466622 := by
    simpa [prefixWord, tailWord_466622, baseEnd_466622] using wordTrace_append hprefix tailTrace_466622
  have hstable : (prefixWord ++ tailWord_466622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466622).length < 2 ^ (prefixWord ++ tailWord_466622).sum := by decide
  have hdescent : baseEnd_466622 < baseStart_466622 := by decide
  rcases family_descends (prefixWord ++ tailWord_466622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466628 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_466628 : Nat := 118140960795 + 466628 * 2 ^ 59
def prefixEnd_466628 : Nat := 4983230072969 + 3 ^ 40 * 466628 * 2
def baseEnd_466628 : Nat := 239604450846305549504023

theorem tailTrace_466628 : CollatzResearch.WordTrace tailWord_466628 prefixEnd_466628 239604450846305549504023 := by
  unfold tailWord_466628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509660676746962281384269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11346214235662616375179025 8509660676746962281384269)
  ·
    refine ⟨3191122753780110855519101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8509660676746962281384269 3191122753780110855519101)
    ·
      refine ⟨1196671032667541570819663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3191122753780110855519101 1196671032667541570819663)
      ·
        refine ⟨1795006549001312356229495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196671032667541570819663 1795006549001312356229495)
        ·
          refine ⟨2692509823501968534344243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795006549001312356229495 2692509823501968534344243)
          ·
            refine ⟨4038764735252952801516365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692509823501968534344243 4038764735252952801516365)
            ·
              refine ⟨1514536775719857300568637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4038764735252952801516365 1514536775719857300568637)
              ·
                refine ⟨567951290894946487713239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514536775719857300568637 567951290894946487713239)
                ·
                  refine ⟨851926936342419731569859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567951290894946487713239 851926936342419731569859)
                  ·
                    refine ⟨1277890404513629597354789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 851926936342419731569859 1277890404513629597354789)
                    ·
                      refine ⟨239604450846305549504023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1277890404513629597354789 239604450846305549504023)
                      ·
                        rfl

theorem cell23_466628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_466628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466628 prefixEnd_466628 := by exact prefixLift 466628
  have htrace : WordTrace (prefixWord ++ tailWord_466628) baseStart_466628 baseEnd_466628 := by
    simpa [prefixWord, tailWord_466628, baseEnd_466628] using wordTrace_append hprefix tailTrace_466628
  have hstable : (prefixWord ++ tailWord_466628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466628).length < 2 ^ (prefixWord ++ tailWord_466628).sum := by decide
  have hdescent : baseEnd_466628 < baseStart_466628 := by decide
  rcases family_descends (prefixWord ++ tailWord_466628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466721 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_466721 : Nat := 118140960795 + 466721 * 2 ^ 59
def prefixEnd_466721 : Nat := 4983230072969 + 3 ^ 40 * 466721 * 2
def baseEnd_466721 : Nat := 239652204547173685641095

theorem tailTrace_466721 : CollatzResearch.WordTrace tailWord_466721 prefixEnd_466721 239652204547173685641095 := by
  unfold tailWord_466721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022713342157001445904017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11348475561438000963936011 17022713342157001445904017)
  ·
    refine ⟨12767035006617751084428013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17022713342157001445904017 12767035006617751084428013)
    ·
      refine ⟨4787638127481656656660505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12767035006617751084428013 4787638127481656656660505)
      ·
        refine ⟨3590728595611242492495379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4787638127481656656660505 3590728595611242492495379)
        ·
          refine ⟨5386092893416863738743069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590728595611242492495379 5386092893416863738743069)
          ·
            refine ⟨2019784835031323902028651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5386092893416863738743069 2019784835031323902028651)
            ·
              refine ⟨3029677252546985853042977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019784835031323902028651 3029677252546985853042977)
              ·
                refine ⟨2272257939410239389782233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3029677252546985853042977 2272257939410239389782233)
                ·
                  refine ⟨1704193454557679542336675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272257939410239389782233 1704193454557679542336675)
                  ·
                    refine ⟨2556290181836519313505013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1704193454557679542336675 2556290181836519313505013)
                    ·
                      refine ⟨239652204547173685641095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2556290181836519313505013 239652204547173685641095)
                      ·
                        rfl

theorem cell23_466721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_466721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466721 prefixEnd_466721 := by exact prefixLift 466721
  have htrace : WordTrace (prefixWord ++ tailWord_466721) baseStart_466721 baseEnd_466721 := by
    simpa [prefixWord, tailWord_466721, baseEnd_466721] using wordTrace_append hprefix tailTrace_466721
  have hstable : (prefixWord ++ tailWord_466721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466721).length < 2 ^ (prefixWord ++ tailWord_466721).sum := by decide
  have hdescent : baseEnd_466721 < baseStart_466721 := by decide
  rcases family_descends (prefixWord ++ tailWord_466721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466765 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_466765 : Nat := 118140960795 + 466765 * 2 ^ 59
def prefixEnd_466765 : Nat := 4983230072969 + 3 ^ 40 * 466765 * 2
def baseEnd_466765 : Nat := 239674797695971513490893

theorem tailTrace_466765 : CollatzResearch.WordTrace tailWord_466765 prefixEnd_466765 239674797695971513490893 := by
  unfold tailWord_466765
  simp only [CollatzResearch.WordTrace]
  refine ⟨17024318153997596960505749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11349545435998397973670499 17024318153997596960505749)
  ·
    refine ⟨798014913468637357523707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17024318153997596960505749 798014913468637357523707)
    ·
      refine ⟨1197022370202956036285561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798014913468637357523707 1197022370202956036285561)
      ·
        refine ⟨897766777652217027214171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197022370202956036285561 897766777652217027214171)
        ·
          refine ⟨1346650166478325540821257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897766777652217027214171 1346650166478325540821257)
          ·
            refine ⟨1009987624858744155615943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346650166478325540821257 1009987624858744155615943)
            ·
              refine ⟨1514981437288116233423915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009987624858744155615943 1514981437288116233423915)
              ·
                refine ⟨2272472155932174350135873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514981437288116233423915 2272472155932174350135873)
                ·
                  refine ⟨1704354116949130762601905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2272472155932174350135873 1704354116949130762601905)
                  ·
                    refine ⟨1278265587711848071951429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1704354116949130762601905 1278265587711848071951429)
                    ·
                      refine ⟨239674797695971513490893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1278265587711848071951429 239674797695971513490893)
                      ·
                        rfl

theorem cell23_466765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_466765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466765 prefixEnd_466765 := by exact prefixLift 466765
  have htrace : WordTrace (prefixWord ++ tailWord_466765) baseStart_466765 baseEnd_466765 := by
    simpa [prefixWord, tailWord_466765, baseEnd_466765] using wordTrace_append hprefix tailTrace_466765
  have hstable : (prefixWord ++ tailWord_466765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466765).length < 2 ^ (prefixWord ++ tailWord_466765).sum := by decide
  have hdescent : baseEnd_466765 < baseStart_466765 := by decide
  rcases family_descends (prefixWord ++ tailWord_466765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466778 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_466778 : Nat := 118140960795 + 466778 * 2 ^ 59
def prefixEnd_466778 : Nat := 4983230072969 + 3 ^ 40 * 466778 * 2
def baseEnd_466778 : Nat := 239681472944479962628333

theorem tailTrace_466778 : CollatzResearch.WordTrace tailWord_466778 prefixEnd_466778 239681472944479962628333 := by
  unfold tailWord_466778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256198075737625045182247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11349861535300333453819325 4256198075737625045182247)
  ·
    refine ⟨6384297113606437567773371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256198075737625045182247 6384297113606437567773371)
    ·
      refine ⟨9576445670409656351660057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384297113606437567773371 9576445670409656351660057)
      ·
        refine ⟨7182334252807242263745043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9576445670409656351660057 7182334252807242263745043)
        ·
          refine ⟨10773501379210863395617565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182334252807242263745043 10773501379210863395617565)
          ·
            refine ⟨4040063017204073773356587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10773501379210863395617565 4040063017204073773356587)
            ·
              refine ⟨6060094525806110660034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040063017204073773356587 6060094525806110660034881)
              ·
                refine ⟨4545070894354582995026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060094525806110660034881 4545070894354582995026161)
                ·
                  refine ⟨3408803170765937246269621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545070894354582995026161 3408803170765937246269621)
                  ·
                    refine ⟨319575297259306616837777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3408803170765937246269621 319575297259306616837777)
                    ·
                      refine ⟨239681472944479962628333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319575297259306616837777 239681472944479962628333)
                      ·
                        rfl

theorem cell23_466778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_466778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466778 prefixEnd_466778 := by exact prefixLift 466778
  have htrace : WordTrace (prefixWord ++ tailWord_466778) baseStart_466778 baseEnd_466778 := by
    simpa [prefixWord, tailWord_466778, baseEnd_466778] using wordTrace_append hprefix tailTrace_466778
  have hstable : (prefixWord ++ tailWord_466778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466778).length < 2 ^ (prefixWord ++ tailWord_466778).sum := by decide
  have hdescent : baseEnd_466778 < baseStart_466778 := by decide
  rcases family_descends (prefixWord ++ tailWord_466778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466788 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_466788 : Nat := 118140960795 + 466788 * 2 ^ 59
def prefixEnd_466788 : Nat := 4983230072969 + 3 ^ 40 * 466788 * 2
def baseEnd_466788 : Nat := 79895535917008307834429

theorem tailTrace_466788 : CollatzResearch.WordTrace tailWord_466788 prefixEnd_466788 79895535917008307834429 := by
  unfold tailWord_466788
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512578516457135944296509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11350104688609514592395345 8512578516457135944296509)
  ·
    refine ⟨3192216943671425979111191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8512578516457135944296509 3192216943671425979111191)
    ·
      refine ⟨4788325415507138968666787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192216943671425979111191 4788325415507138968666787)
      ·
        refine ⟨7182488123260708453000181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788325415507138968666787 7182488123260708453000181)
        ·
          refine ⟨673358261555691417468767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7182488123260708453000181 673358261555691417468767)
          ·
            refine ⟨1010037392333537126203151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673358261555691417468767 1010037392333537126203151)
            ·
              refine ⟨1515056088500305689304727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010037392333537126203151 1515056088500305689304727)
              ·
                refine ⟨2272584132750458533957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515056088500305689304727 2272584132750458533957091)
                ·
                  refine ⟨3408876199125687800935637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2272584132750458533957091 3408876199125687800935637)
                  ·
                    refine ⟨79895535917008307834429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3408876199125687800935637 79895535917008307834429)
                    ·
                      rfl

theorem cell23_466788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_466788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466788 prefixEnd_466788 := by exact prefixLift 466788
  have htrace : WordTrace (prefixWord ++ tailWord_466788) baseStart_466788 baseEnd_466788 := by
    simpa [prefixWord, tailWord_466788, baseEnd_466788] using wordTrace_append hprefix tailTrace_466788
  have hstable : (prefixWord ++ tailWord_466788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466788).length < 2 ^ (prefixWord ++ tailWord_466788).sum := by decide
  have hdescent : baseEnd_466788 < baseStart_466788 := by decide
  rcases family_descends (prefixWord ++ tailWord_466788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466821 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_466821 : Nat := 118140960795 + 466821 * 2 ^ 59
def prefixEnd_466821 : Nat := 4983230072969 + 3 ^ 40 * 466821 * 2
def baseEnd_466821 : Nat := 239703552612623294390635

theorem tailTrace_466821 : CollatzResearch.WordTrace tailWord_466821 prefixEnd_466821 239703552612623294390635 := by
  unfold tailWord_466821
  simp only [CollatzResearch.WordTrace]
  refine ⟨17026360641794718524544317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11350907094529812349696211 17026360641794718524544317)
  ·
    refine ⟨6384885240673019446704119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17026360641794718524544317 6384885240673019446704119)
    ·
      refine ⟨9577327861009529170056179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384885240673019446704119 9577327861009529170056179)
      ·
        refine ⟨14365991791514293755084269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9577327861009529170056179 14365991791514293755084269)
        ·
          refine ⟨5387246921817860158156601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14365991791514293755084269 5387246921817860158156601)
          ·
            refine ⟨4040435191363395118617451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5387246921817860158156601 4040435191363395118617451)
            ·
              refine ⟨6060652787045092677926177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040435191363395118617451 6060652787045092677926177)
              ·
                refine ⟨4545489590283819508444633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6060652787045092677926177 4545489590283819508444633)
                ·
                  refine ⟨3409117192712864631333475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4545489590283819508444633 3409117192712864631333475)
                  ·
                    refine ⟨5113675789069296947000213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3409117192712864631333475 5113675789069296947000213)
                    ·
                      refine ⟨239703552612623294390635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5113675789069296947000213 239703552612623294390635)
                      ·
                        rfl

theorem cell23_466821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_466821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466821 prefixEnd_466821 := by exact prefixLift 466821
  have htrace : WordTrace (prefixWord ++ tailWord_466821) baseStart_466821 baseEnd_466821 := by
    simpa [prefixWord, tailWord_466821, baseEnd_466821] using wordTrace_append hprefix tailTrace_466821
  have hstable : (prefixWord ++ tailWord_466821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466821).length < 2 ^ (prefixWord ++ tailWord_466821).sum := by decide
  have hdescent : baseEnd_466821 < baseStart_466821 := by decide
  rcases family_descends (prefixWord ++ tailWord_466821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466852 : List Nat := [2, 3, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_466852 : Nat := 118140960795 + 466852 * 2 ^ 59
def prefixEnd_466852 : Nat := 4983230072969 + 3 ^ 40 * 466852 * 2
def baseEnd_466852 : Nat := 79906490170970891034331

theorem tailTrace_466852 : CollatzResearch.WordTrace tailWord_466852 prefixEnd_466852 79906490170970891034331 := by
  unfold tailWord_466852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513745652341205409461405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11351660869788273879281873 8513745652341205409461405)
  ·
    refine ⟨3192654619627952028548027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8513745652341205409461405 3192654619627952028548027)
    ·
      refine ⟨4788981929441928042822041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3192654619627952028548027 4788981929441928042822041)
      ·
        refine ⟨3591736447081446032116531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4788981929441928042822041 3591736447081446032116531)
        ·
          refine ⟨5387604670622169048174797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591736447081446032116531 5387604670622169048174797)
          ·
            refine ⟨2020351751483313393065549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5387604670622169048174797 2020351751483313393065549)
            ·
              refine ⟨757631906806242522399581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2020351751483313393065549 757631906806242522399581)
              ·
                refine ⟨284111965052340945899843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757631906806242522399581 284111965052340945899843)
                ·
                  refine ⟨426167947578511418849765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284111965052340945899843 426167947578511418849765)
                  ·
                    refine ⟨79906490170970891034331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426167947578511418849765 79906490170970891034331)
                    ·
                      rfl

theorem cell23_466852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_466852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466852 prefixEnd_466852 := by exact prefixLift 466852
  have htrace : WordTrace (prefixWord ++ tailWord_466852) baseStart_466852 baseEnd_466852 := by
    simpa [prefixWord, tailWord_466852, baseEnd_466852] using wordTrace_append hprefix tailTrace_466852
  have hstable : (prefixWord ++ tailWord_466852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466852).length < 2 ^ (prefixWord ++ tailWord_466852).sum := by decide
  have hdescent : baseEnd_466852 < baseStart_466852 := by decide
  rcases family_descends (prefixWord ++ tailWord_466852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466869 : List Nat := [1, 3, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_466869 : Nat := 118140960795 + 466869 * 2 ^ 59
def prefixEnd_466869 : Nat := 4983230072969 + 3 ^ 40 * 466869 * 2
def baseEnd_466869 : Nat := 79909399894679702196805

theorem tailTrace_466869 : CollatzResearch.WordTrace tailWord_466869 prefixEnd_466869 79909399894679702196805 := by
  unfold tailWord_466869
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028111345620822722291661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11352074230413881814861107 17028111345620822722291661)
  ·
    refine ⟨6385541754607808520859373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17028111345620822722291661 6385541754607808520859373)
    ·
      refine ⟨2394578157977928195322265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6385541754607808520859373 2394578157977928195322265)
      ·
        refine ⟨1795933618483446146491699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394578157977928195322265 1795933618483446146491699)
        ·
          refine ⟨2693900427725169219737549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795933618483446146491699 2693900427725169219737549)
          ·
            refine ⟨1010212660396938457401581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2693900427725169219737549 1010212660396938457401581)
            ·
              refine ⟨378829747648851921525593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010212660396938457401581 378829747648851921525593)
              ·
                refine ⟨284122310736638941144195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378829747648851921525593 284122310736638941144195)
                ·
                  refine ⟨426183466104958411716293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284122310736638941144195 426183466104958411716293)
                  ·
                    refine ⟨79909399894679702196805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426183466104958411716293 79909399894679702196805)
                    ·
                      rfl

theorem cell23_466869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_466869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466869 prefixEnd_466869 := by exact prefixLift 466869
  have htrace : WordTrace (prefixWord ++ tailWord_466869) baseStart_466869 baseEnd_466869 := by
    simpa [prefixWord, tailWord_466869, baseEnd_466869] using wordTrace_append hprefix tailTrace_466869
  have hstable : (prefixWord ++ tailWord_466869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466869).length < 2 ^ (prefixWord ++ tailWord_466869).sum := by decide
  have hdescent : baseEnd_466869 < baseStart_466869 := by decide
  rcases family_descends (prefixWord ++ tailWord_466869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466871 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_466871 : Nat := 118140960795 + 466871 * 2 ^ 59
def prefixEnd_466871 : Nat := 4983230072969 + 3 ^ 40 * 466871 * 2
def baseEnd_466871 : Nat := 239729226645348098765405

theorem tailTrace_466871 : CollatzResearch.WordTrace tailWord_466871 prefixEnd_466871 239729226645348098765405 := by
  unfold tailWord_466871
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028184291613577063864467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11352122861075718042576311 17028184291613577063864467)
  ·
    refine ⟨25542276437420365595796701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17028184291613577063864467 25542276437420365595796701)
    ·
      refine ⟨9578353664032637098423763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25542276437420365595796701 9578353664032637098423763)
      ·
        refine ⟨14367530496048955647635645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578353664032637098423763 14367530496048955647635645)
        ·
          refine ⟨5387823936018358367863367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14367530496048955647635645 5387823936018358367863367)
          ·
            refine ⟨8081735904027537551795051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387823936018358367863367 8081735904027537551795051)
            ·
              refine ⟨12122603856041306327692577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8081735904027537551795051 12122603856041306327692577)
              ·
                refine ⟨9091952892030979745769433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12122603856041306327692577 9091952892030979745769433)
                ·
                  refine ⟨6818964669023234809327075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9091952892030979745769433 6818964669023234809327075)
                  ·
                    refine ⟨10228447003534852213990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6818964669023234809327075 10228447003534852213990613)
                    ·
                      refine ⟨239729226645348098765405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10228447003534852213990613 239729226645348098765405)
                      ·
                        rfl

theorem cell23_466871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_466871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466871 prefixEnd_466871 := by exact prefixLift 466871
  have htrace : WordTrace (prefixWord ++ tailWord_466871) baseStart_466871 baseEnd_466871 := by
    simpa [prefixWord, tailWord_466871, baseEnd_466871] using wordTrace_append hprefix tailTrace_466871
  have hstable : (prefixWord ++ tailWord_466871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466871).length < 2 ^ (prefixWord ++ tailWord_466871).sum := by decide
  have hdescent : baseEnd_466871 < baseStart_466871 := by decide
  rcases family_descends (prefixWord ++ tailWord_466871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466926 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_466926 : Nat := 118140960795 + 466926 * 2 ^ 59
def prefixEnd_466926 : Nat := 4983230072969 + 3 ^ 40 * 466926 * 2
def baseEnd_466926 : Nat := 239757468081345383577653

theorem tailTrace_466926 : CollatzResearch.WordTrace tailWord_466926 prefixEnd_466926 239757468081345383577653 := by
  unfold tailWord_466926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128773788301790182139579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11353460204276214304744421 2128773788301790182139579)
  ·
    refine ⟨3193160682452685273209369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2128773788301790182139579 3193160682452685273209369)
    ·
      refine ⟨2394870511839513954907027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3193160682452685273209369 2394870511839513954907027)
      ·
        refine ⟨3592305767759270932360541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394870511839513954907027 3592305767759270932360541)
        ·
          refine ⟨1347114662909726599635203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3592305767759270932360541 1347114662909726599635203)
          ·
            refine ⟨2020671994364589899452805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347114662909726599635203 2020671994364589899452805)
            ·
              refine ⟨378875998943360606147401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2020671994364589899452805 378875998943360606147401)
              ·
                refine ⟨284156999207520454610551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378875998943360606147401 284156999207520454610551)
                ·
                  refine ⟨426235498811280681915827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284156999207520454610551 426235498811280681915827)
                  ·
                    refine ⟨639353248216921022873741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426235498811280681915827 639353248216921022873741)
                    ·
                      refine ⟨239757468081345383577653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 639353248216921022873741 239757468081345383577653)
                      ·
                        rfl

theorem cell23_466926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_466926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466926 prefixEnd_466926 := by exact prefixLift 466926
  have htrace : WordTrace (prefixWord ++ tailWord_466926) baseStart_466926 baseEnd_466926 := by
    simpa [prefixWord, tailWord_466926, baseEnd_466926] using wordTrace_append hprefix tailTrace_466926
  have hstable : (prefixWord ++ tailWord_466926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466926).length < 2 ^ (prefixWord ++ tailWord_466926).sum := by decide
  have hdescent : baseEnd_466926 < baseStart_466926 := by decide
  rcases family_descends (prefixWord ++ tailWord_466926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466942 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_466942 : Nat := 118140960795 + 466942 * 2 ^ 59
def prefixEnd_466942 : Nat := 4983230072969 + 3 ^ 40 * 466942 * 2
def baseEnd_466942 : Nat := 79921894590605773659193

theorem tailTrace_466942 : CollatzResearch.WordTrace tailWord_466942 prefixEnd_466942 79921894590605773659193 := by
  unfold tailWord_466942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128846734294544523712385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11353849249570904126466053 2128846734294544523712385)
  ·
    refine ⟨1596635050720908392784289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2128846734294544523712385 1596635050720908392784289)
    ·
      refine ⟨1197476288040681294588217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596635050720908392784289 1197476288040681294588217)
      ·
        refine ⟨898107216030510970941163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197476288040681294588217 898107216030510970941163)
        ·
          refine ⟨1347160824045766456411745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898107216030510970941163 1347160824045766456411745)
          ·
            refine ⟨1010370618034324842308809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347160824045766456411745 1010370618034324842308809)
            ·
              refine ⟨757777963525743631731607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010370618034324842308809 757777963525743631731607)
              ·
                refine ⟨1136666945288615447597411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757777963525743631731607 1136666945288615447597411)
                ·
                  refine ⟨1705000417932923171396117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136666945288615447597411 1705000417932923171396117)
                  ·
                    refine ⟨79921894590605773659193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1705000417932923171396117 79921894590605773659193)
                    ·
                      rfl

theorem cell23_466942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_466942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466942 prefixEnd_466942 := by exact prefixLift 466942
  have htrace : WordTrace (prefixWord ++ tailWord_466942) baseStart_466942 baseEnd_466942 := by
    simpa [prefixWord, tailWord_466942, baseEnd_466942] using wordTrace_append hprefix tailTrace_466942
  have hstable : (prefixWord ++ tailWord_466942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466942).length < 2 ^ (prefixWord ++ tailWord_466942).sum := by decide
  have hdescent : baseEnd_466942 < baseStart_466942 := by decide
  rcases family_descends (prefixWord ++ tailWord_466942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466945 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_466945 : Nat := 118140960795 + 466945 * 2 ^ 59
def prefixEnd_466945 : Nat := 4983230072969 + 3 ^ 40 * 466945 * 2
def baseEnd_466945 : Nat := 239767224213780809240065

theorem tailTrace_466945 : CollatzResearch.WordTrace tailWord_466945 prefixEnd_466945 239767224213780809240065 := by
  unfold tailWord_466945
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030883293345487702058289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11353922195563658468038859 17030883293345487702058289)
  ·
    refine ⟨12773162470009115776543717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17030883293345487702058289 12773162470009115776543717)
    ·
      refine ⟨2394967963126709208101947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12773162470009115776543717 2394967963126709208101947)
      ·
        refine ⟨3592451944690063812152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394967963126709208101947 3592451944690063812152921)
        ·
          refine ⟨2694338958517547859114691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3592451944690063812152921 2694338958517547859114691)
          ·
            refine ⟨4041508437776321788672037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694338958517547859114691 4041508437776321788672037)
            ·
              refine ⟨757782832083060335376007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4041508437776321788672037 757782832083060335376007)
              ·
                refine ⟨1136674248124590503064011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757782832083060335376007 1136674248124590503064011)
                ·
                  refine ⟨1705011372186885754596017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136674248124590503064011 1705011372186885754596017)
                  ·
                    refine ⟨1278758529140164315947013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705011372186885754596017 1278758529140164315947013)
                    ·
                      refine ⟨239767224213780809240065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1278758529140164315947013 239767224213780809240065)
                      ·
                        rfl

theorem cell23_466945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_466945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466945 prefixEnd_466945 := by exact prefixLift 466945
  have htrace : WordTrace (prefixWord ++ tailWord_466945) baseStart_466945 baseEnd_466945 := by
    simpa [prefixWord, tailWord_466945, baseEnd_466945] using wordTrace_append hprefix tailTrace_466945
  have hstable : (prefixWord ++ tailWord_466945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466945).length < 2 ^ (prefixWord ++ tailWord_466945).sum := by decide
  have hdescent : baseEnd_466945 < baseStart_466945 := by decide
  rcases family_descends (prefixWord ++ tailWord_466945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466988 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_466988 : Nat := 118140960795 + 466988 * 2 ^ 59
def prefixEnd_466988 : Nat := 4983230072969 + 3 ^ 40 * 466988 * 2
def baseEnd_466988 : Nat := 239789303881924141002367

theorem tailTrace_466988 : CollatzResearch.WordTrace tailWord_466988 prefixEnd_466988 239789303881924141002367 := by
  unfold tailWord_466988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516225816094853022936809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11354967754793137363915745 8516225816094853022936809)
  ·
    refine ⟨6387169362071139767202607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8516225816094853022936809 6387169362071139767202607)
    ·
      refine ⟨9580754043106709650803911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387169362071139767202607 9580754043106709650803911)
      ·
        refine ⟨14371131064660064476205867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9580754043106709650803911 14371131064660064476205867)
        ·
          refine ⟨21556696596990096714308801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14371131064660064476205867 21556696596990096714308801)
          ·
            refine ⟨16167522447742572535731601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21556696596990096714308801 16167522447742572535731601)
            ·
              refine ⟨12125641835806929401798701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16167522447742572535731601 12125641835806929401798701)
              ·
                refine ⟨4547115688427598525674513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12125641835806929401798701 4547115688427598525674513)
                ·
                  refine ⟨3410336766320698894255885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547115688427598525674513 3410336766320698894255885)
                  ·
                    refine ⟨1278876287370262085345957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410336766320698894255885 1278876287370262085345957)
                    ·
                      refine ⟨239789303881924141002367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1278876287370262085345957 239789303881924141002367)
                      ·
                        rfl

theorem cell23_466988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_466988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466988 prefixEnd_466988 := by exact prefixLift 466988
  have htrace : WordTrace (prefixWord ++ tailWord_466988) baseStart_466988 baseEnd_466988 := by
    simpa [prefixWord, tailWord_466988, baseEnd_466988] using wordTrace_append hprefix tailTrace_466988
  have hstable : (prefixWord ++ tailWord_466988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466988).length < 2 ^ (prefixWord ++ tailWord_466988).sum := by decide
  have hdescent : baseEnd_466988 < baseStart_466988 := by decide
  rcases family_descends (prefixWord ++ tailWord_466988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466996 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_466996 : Nat := 118140960795 + 466996 * 2 ^ 59
def prefixEnd_466996 : Nat := 4983230072969 + 3 ^ 40 * 466996 * 2
def baseEnd_466996 : Nat := 239793411727160109702331

theorem tailTrace_466996 : CollatzResearch.WordTrace tailWord_466996 prefixEnd_466996 239793411727160109702331 := by
  unfold tailWord_466996
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516371708080361706082421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11355162277440482274776561 8516371708080361706082421)
  ·
    refine ⟨798409847632533909945227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8516371708080361706082421 798409847632533909945227)
    ·
      refine ⟨1197614771448800864917841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798409847632533909945227 1197614771448800864917841)
      ·
        refine ⟨898211078586600648688381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1197614771448800864917841 898211078586600648688381)
        ·
          refine ⟨336829154469975243258143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898211078586600648688381 336829154469975243258143)
          ·
            refine ⟨505243731704962864887215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336829154469975243258143 505243731704962864887215)
            ·
              refine ⟨757865597557444297330823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505243731704962864887215 757865597557444297330823)
              ·
                refine ⟨1136798396336166445996235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757865597557444297330823 1136798396336166445996235)
                ·
                  refine ⟨1705197594504249668994353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1136798396336166445996235 1705197594504249668994353)
                  ·
                    refine ⟨1278898195878187251745765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1705197594504249668994353 1278898195878187251745765)
                    ·
                      refine ⟨239793411727160109702331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1278898195878187251745765 239793411727160109702331)
                      ·
                        rfl

theorem cell23_466996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_466996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_466996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_466996 prefixEnd_466996 := by exact prefixLift 466996
  have htrace : WordTrace (prefixWord ++ tailWord_466996) baseStart_466996 baseEnd_466996 := by
    simpa [prefixWord, tailWord_466996, baseEnd_466996] using wordTrace_append hprefix tailTrace_466996
  have hstable : (prefixWord ++ tailWord_466996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466996).length < 2 ^ (prefixWord ++ tailWord_466996).sum := by decide
  have hdescent : baseEnd_466996 < baseStart_466996 := by decide
  rcases family_descends (prefixWord ++ tailWord_466996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467009 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_467009 : Nat := 118140960795 + 467009 * 2 ^ 59
def prefixEnd_467009 : Nat := 4983230072969 + 3 ^ 40 * 467009 * 2
def baseEnd_467009 : Nat := 239800086975668558839771

theorem tailTrace_467009 : CollatzResearch.WordTrace tailWord_467009 prefixEnd_467009 239800086975668558839771 := by
  unfold tailWord_467009
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033217565113626632388081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11355478376742417754925387 17033217565113626632388081)
  ·
    refine ⟨12774913173835219974291061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17033217565113626632388081 12774913173835219974291061)
    ·
      refine ⟨1197648110047051872589787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12774913173835219974291061 1197648110047051872589787)
      ·
        refine ⟨1796472165070577808884681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197648110047051872589787 1796472165070577808884681)
        ·
          refine ⟨1347354123802933356663511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796472165070577808884681 1347354123802933356663511)
          ·
            refine ⟨2021031185704400034995267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347354123802933356663511 2021031185704400034995267)
            ·
              refine ⟨3031546778556600052492901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021031185704400034995267 3031546778556600052492901)
              ·
                refine ⟨568415020979362509842419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3031546778556600052492901 568415020979362509842419)
                ·
                  refine ⟨852622531469043764763629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568415020979362509842419 852622531469043764763629)
                  ·
                    refine ⟨319733449300891411786361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 852622531469043764763629 319733449300891411786361)
                    ·
                      refine ⟨239800086975668558839771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319733449300891411786361 239800086975668558839771)
                      ·
                        rfl

theorem cell23_467009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_467009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467009 prefixEnd_467009 := by exact prefixLift 467009
  have htrace : WordTrace (prefixWord ++ tailWord_467009) baseStart_467009 baseEnd_467009 := by
    simpa [prefixWord, tailWord_467009, baseEnd_467009] using wordTrace_append hprefix tailTrace_467009
  have hstable : (prefixWord ++ tailWord_467009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467009).length < 2 ^ (prefixWord ++ tailWord_467009).sum := by decide
  have hdescent : baseEnd_467009 < baseStart_467009 := by decide
  rcases family_descends (prefixWord ++ tailWord_467009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467045 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 7]
def baseStart_467045 : Nat := 118140960795 + 467045 * 2 ^ 59
def prefixEnd_467045 : Nat := 4983230072969 + 3 ^ 40 * 467045 * 2
def baseEnd_467045 : Nat := 26646508031025601998845

theorem tailTrace_467045 : CollatzResearch.WordTrace tailWord_467045 prefixEnd_467045 26646508031025601998845 := by
  unfold tailWord_467045
  simp only [CollatzResearch.WordTrace]
  refine ⟨17034530592983204780698589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11356353728655469853799059 17034530592983204780698589)
  ·
    refine ⟨6387948972368701792761971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17034530592983204780698589 6387948972368701792761971)
    ·
      refine ⟨9581923458553052689142957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387948972368701792761971 9581923458553052689142957)
      ·
        refine ⟨3593221296957394758428609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9581923458553052689142957 3593221296957394758428609)
        ·
          refine ⟨2694915972718046068821457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3593221296957394758428609 2694915972718046068821457)
          ·
            refine ⟨2021186979538534551616093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694915972718046068821457 2021186979538534551616093)
            ·
              refine ⟨757945117326950456856035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2021186979538534551616093 757945117326950456856035)
              ·
                refine ⟨1136917675990425685284053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757945117326950456856035 1136917675990425685284053)
                ·
                  refine ⟨26646508031025601998845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1136917675990425685284053 26646508031025601998845)
                  ·
                    rfl

theorem cell23_467045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_467045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467045 prefixEnd_467045 := by exact prefixLift 467045
  have htrace : WordTrace (prefixWord ++ tailWord_467045) baseStart_467045 baseEnd_467045 := by
    simpa [prefixWord, tailWord_467045, baseEnd_467045] using wordTrace_append hprefix tailTrace_467045
  have hstable : (prefixWord ++ tailWord_467045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467045).length < 2 ^ (prefixWord ++ tailWord_467045).sum := by decide
  have hdescent : baseEnd_467045 < baseStart_467045 := by decide
  rcases family_descends (prefixWord ++ tailWord_467045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467056 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2]
def baseStart_467056 : Nat := 118140960795 + 467056 * 2 ^ 59
def prefixEnd_467056 : Nat := 4983230072969 + 3 ^ 40 * 467056 * 2
def baseEnd_467056 : Nat := 239824220566429874952055

theorem tailTrace_467056 : CollatzResearch.WordTrace tailWord_467056 prefixEnd_467056 239824220566429874952055 := by
  unfold tailWord_467056
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517465897971676829674511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11356621197295569106232681 8517465897971676829674511)
  ·
    refine ⟨12776198846957515244511767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517465897971676829674511 12776198846957515244511767)
    ·
      refine ⟨19164298270436272866767651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12776198846957515244511767 19164298270436272866767651)
      ·
        refine ⟨28746447405654409300151477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19164298270436272866767651 28746447405654409300151477)
        ·
          refine ⟨2694979444280100871889201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28746447405654409300151477 2694979444280100871889201)
          ·
            refine ⟨2021234583210075653916901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694979444280100871889201 2021234583210075653916901)
            ·
              refine ⟨378981484351889185109419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2021234583210075653916901 378981484351889185109419)
              ·
                refine ⟨568472226527833777664129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378981484351889185109419 568472226527833777664129)
                ·
                  refine ⟨426354169895875333248097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568472226527833777664129 426354169895875333248097)
                  ·
                    refine ⟨319765627421906499936073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 426354169895875333248097 319765627421906499936073)
                    ·
                      refine ⟨239824220566429874952055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319765627421906499936073 239824220566429874952055)
                      ·
                        rfl

theorem cell23_467056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2].length) (baseStart_467056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467056 prefixEnd_467056 := by exact prefixLift 467056
  have htrace : WordTrace (prefixWord ++ tailWord_467056) baseStart_467056 baseEnd_467056 := by
    simpa [prefixWord, tailWord_467056, baseEnd_467056] using wordTrace_append hprefix tailTrace_467056
  have hstable : (prefixWord ++ tailWord_467056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467056).length < 2 ^ (prefixWord ++ tailWord_467056).sum := by decide
  have hdescent : baseEnd_467056 < baseStart_467056 := by decide
  rcases family_descends (prefixWord ++ tailWord_467056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467075 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 2, 5]
def baseStart_467075 : Nat := 118140960795 + 467075 * 2 ^ 59
def prefixEnd_467075 : Nat := 4983230072969 + 3 ^ 40 * 467075 * 2
def baseEnd_467075 : Nat := 79944658899621766871489

theorem tailTrace_467075 : CollatzResearch.WordTrace tailWord_467075 prefixEnd_467075 79944658899621766871489 := by
  unfold tailWord_467075
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035624782874519904290679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11357083188583013269527119 17035624782874519904290679)
  ·
    refine ⟨25553437174311779856436019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17035624782874519904290679 25553437174311779856436019)
    ·
      refine ⟨38330155761467669784654029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25553437174311779856436019 38330155761467669784654029)
      ·
        refine ⟨14373808410550376169245261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38330155761467669784654029 14373808410550376169245261)
        ·
          refine ⟨5390178153956391063466973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14373808410550376169245261 5390178153956391063466973)
          ·
            refine ⟨2021316807733646648800115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5390178153956391063466973 2021316807733646648800115)
            ·
              refine ⟨3031975211600469973200173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021316807733646648800115 3031975211600469973200173)
              ·
                refine ⟨1136990704350176239950065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3031975211600469973200173 1136990704350176239950065)
                ·
                  refine ⟨852743028262632179962549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136990704350176239950065 852743028262632179962549)
                  ·
                    refine ⟨79944658899621766871489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 852743028262632179962549 79944658899621766871489)
                    ·
                      rfl

theorem cell23_467075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].length) (baseStart_467075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467075 prefixEnd_467075 := by exact prefixLift 467075
  have htrace : WordTrace (prefixWord ++ tailWord_467075) baseStart_467075 baseEnd_467075 := by
    simpa [prefixWord, tailWord_467075, baseEnd_467075] using wordTrace_append hprefix tailTrace_467075
  have hstable : (prefixWord ++ tailWord_467075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467075).length < 2 ^ (prefixWord ++ tailWord_467075).sum := by decide
  have hdescent : baseEnd_467075 < baseStart_467075 := by decide
  rcases family_descends (prefixWord ++ tailWord_467075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467096 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 5]
def baseStart_467096 : Nat := 118140960795 + 467096 * 2 ^ 59
def prefixEnd_467096 : Nat := 4983230072969 + 3 ^ 40 * 467096 * 2
def baseEnd_467096 : Nat := 26649417754734413161319

theorem tailTrace_467096 : CollatzResearch.WordTrace tailWord_467096 prefixEnd_467096 26649417754734413161319 := by
  unfold tailWord_467096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8518195357899220245402571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11357593810532293660536761 8518195357899220245402571)
  ·
    refine ⟨12777293036848830368103857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8518195357899220245402571 12777293036848830368103857)
    ·
      refine ⟨9582969777636622776077893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12777293036848830368103857 9582969777636622776077893)
      ·
        refine ⟨1796806833306866770514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9582969777636622776077893 1796806833306866770514605)
        ·
          refine ⟨673802562490075038942977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796806833306866770514605 673802562490075038942977)
          ·
            refine ⟨505351921867556279207233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673802562490075038942977 505351921867556279207233)
            ·
              refine ⟨379013941400667209405425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505351921867556279207233 379013941400667209405425)
              ·
                refine ⟨284260456050500407054069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379013941400667209405425 284260456050500407054069)
                ·
                  refine ⟨26649417754734413161319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284260456050500407054069 26649417754734413161319)
                  ·
                    rfl

theorem cell23_467096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 5].length) (baseStart_467096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467096 prefixEnd_467096 := by exact prefixLift 467096
  have htrace : WordTrace (prefixWord ++ tailWord_467096) baseStart_467096 baseEnd_467096 := by
    simpa [prefixWord, tailWord_467096, baseEnd_467096] using wordTrace_append hprefix tailTrace_467096
  have hstable : (prefixWord ++ tailWord_467096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467096).length < 2 ^ (prefixWord ++ tailWord_467096).sum := by decide
  have hdescent : baseEnd_467096 < baseStart_467096 := by decide
  rcases family_descends (prefixWord ++ tailWord_467096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467122 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_467122 : Nat := 118140960795 + 467122 * 2 ^ 59
def prefixEnd_467122 : Nat := 4983230072969 + 3 ^ 40 * 467122 * 2
def baseEnd_467122 : Nat := 79952703429875538908917

theorem tailTrace_467122 : CollatzResearch.WordTrace tailWord_467122 prefixEnd_467122 79952703429875538908917 := by
  unfold tailWord_467122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259334753426061732812905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11358226009136164620834413 4259334753426061732812905)
  ·
    refine ⟨3194501065069546299609679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4259334753426061732812905 3194501065069546299609679)
    ·
      refine ⟨4791751597604319449414519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194501065069546299609679 4791751597604319449414519)
      ·
        refine ⟨7187627396406479174121779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791751597604319449414519 7187627396406479174121779)
        ·
          refine ⟨10781441094609718761182669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187627396406479174121779 10781441094609718761182669)
          ·
            refine ⟨4043040410478644535443501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10781441094609718761182669 4043040410478644535443501)
            ·
              refine ⟨1516140153929491700791313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4043040410478644535443501 1516140153929491700791313)
              ·
                refine ⟨1137105115447118775593485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516140153929491700791313 1137105115447118775593485)
                ·
                  refine ⟨426414418292669540847557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137105115447118775593485 426414418292669540847557)
                  ·
                    refine ⟨79952703429875538908917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426414418292669540847557 79952703429875538908917)
                    ·
                      rfl

theorem cell23_467122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_467122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467122 prefixEnd_467122 := by exact prefixLift 467122
  have htrace : WordTrace (prefixWord ++ tailWord_467122) baseStart_467122 baseEnd_467122 := by
    simpa [prefixWord, tailWord_467122, baseEnd_467122] using wordTrace_append hprefix tailTrace_467122
  have hstable : (prefixWord ++ tailWord_467122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467122).length < 2 ^ (prefixWord ++ tailWord_467122).sum := by decide
  have hdescent : baseEnd_467122 < baseStart_467122 := by decide
  rcases family_descends (prefixWord ++ tailWord_467122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467212 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_467212 : Nat := 118140960795 + 467212 * 2 ^ 59
def prefixEnd_467212 : Nat := 4983230072969 + 3 ^ 40 * 467212 * 2
def baseEnd_467212 : Nat := 79968107849510421533779

theorem tailTrace_467212 : CollatzResearch.WordTrace tailWord_467212 prefixEnd_467212 79968107849510421533779 := by
  unfold tailWord_467212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520310791689096151013945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11360414388918794868018593 8520310791689096151013945)
  ·
    refine ⟨6390233093766822113260459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8520310791689096151013945 6390233093766822113260459)
    ·
      refine ⟨9585349640650233169890689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390233093766822113260459 9585349640650233169890689)
      ·
        refine ⟨7189012230487674877418017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9585349640650233169890689 7189012230487674877418017)
        ·
          refine ⟨5391759172865756158063513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7189012230487674877418017 5391759172865756158063513)
          ·
            refine ⟨4043819379649317118547635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391759172865756158063513 4043819379649317118547635)
            ·
              refine ⟨6065729069473975677821453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043819379649317118547635 6065729069473975677821453)
              ·
                refine ⟨2274648401052740879183045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6065729069473975677821453 2274648401052740879183045)
                ·
                  refine ⟨426496575197388914846821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274648401052740879183045 426496575197388914846821)
                  ·
                    refine ⟨79968107849510421533779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426496575197388914846821 79968107849510421533779)
                    ·
                      rfl

theorem cell23_467212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_467212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467212 prefixEnd_467212 := by exact prefixLift 467212
  have htrace : WordTrace (prefixWord ++ tailWord_467212) baseStart_467212 baseEnd_467212 := by
    simpa [prefixWord, tailWord_467212, baseEnd_467212] using wordTrace_append hprefix tailTrace_467212
  have hstable : (prefixWord ++ tailWord_467212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467212).length < 2 ^ (prefixWord ++ tailWord_467212).sum := by decide
  have hdescent : baseEnd_467212 < baseStart_467212 := by decide
  rcases family_descends (prefixWord ++ tailWord_467212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467232 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_467232 : Nat := 118140960795 + 467232 * 2 ^ 59
def prefixEnd_467232 : Nat := 4983230072969 + 3 ^ 40 * 467232 * 2
def baseEnd_467232 : Nat := 239914593161621186351245

theorem tailTrace_467232 : CollatzResearch.WordTrace tailWord_467232 prefixEnd_467232 239914593161621186351245 := by
  unfold tailWord_467232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520675521652867858877975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11360900695537157145170633 8520675521652867858877975)
  ·
    refine ⟨12781013282479301788316963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8520675521652867858877975 12781013282479301788316963)
    ·
      refine ⟨19171519923718952682475445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12781013282479301788316963 19171519923718952682475445)
      ·
        refine ⟨1797329992848651813982073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19171519923718952682475445 1797329992848651813982073)
        ·
          refine ⟨1347997494636488860486555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797329992848651813982073 1347997494636488860486555)
          ·
            refine ⟨2021996241954733290729833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347997494636488860486555 2021996241954733290729833)
            ·
              refine ⟨1516497181466049968047375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021996241954733290729833 1516497181466049968047375)
              ·
                refine ⟨2274745772199074952071063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516497181466049968047375 2274745772199074952071063)
                ·
                  refine ⟨3412118658298612428106595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274745772199074952071063 3412118658298612428106595)
                  ·
                    refine ⟨5118177987447918642159893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3412118658298612428106595 5118177987447918642159893)
                    ·
                      refine ⟨239914593161621186351245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5118177987447918642159893 239914593161621186351245)
                      ·
                        rfl

theorem cell23_467232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_467232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467232 prefixEnd_467232 := by exact prefixLift 467232
  have htrace : WordTrace (prefixWord ++ tailWord_467232) baseStart_467232 baseEnd_467232 := by
    simpa [prefixWord, tailWord_467232, baseEnd_467232] using wordTrace_append hprefix tailTrace_467232
  have hstable : (prefixWord ++ tailWord_467232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467232).length < 2 ^ (prefixWord ++ tailWord_467232).sum := by decide
  have hdescent : baseEnd_467232 < baseStart_467232 := by decide
  rcases family_descends (prefixWord ++ tailWord_467232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467236 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_467236 : Nat := 118140960795 + 467236 * 2 ^ 59
def prefixEnd_467236 : Nat := 4983230072969 + 3 ^ 40 * 467236 * 2
def baseEnd_467236 : Nat := 239916647084239170701227

theorem tailTrace_467236 : CollatzResearch.WordTrace tailWord_467236 prefixEnd_467236 239916647084239170701227 := by
  unfold tailWord_467236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520748467645622200450781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11360997956860829600601041 8520748467645622200450781)
  ·
    refine ⟨3195280675367108325169043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8520748467645622200450781 3195280675367108325169043)
    ·
      refine ⟨4792921013050662487753565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3195280675367108325169043 4792921013050662487753565)
      ·
        refine ⟨1797345379893998432907587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4792921013050662487753565 1797345379893998432907587)
        ·
          refine ⟨2696018069840997649361381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797345379893998432907587 2696018069840997649361381)
          ·
            refine ⟨505503388095187059255259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2696018069840997649361381 505503388095187059255259)
            ·
              refine ⟨758255082142780588882889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505503388095187059255259 758255082142780588882889)
              ·
                refine ⟨568691311607085441662167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758255082142780588882889 568691311607085441662167)
                ·
                  refine ⟨853036967410628162493251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568691311607085441662167 853036967410628162493251)
                  ·
                    refine ⟨1279555451115942243739877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 853036967410628162493251 1279555451115942243739877)
                    ·
                      refine ⟨239916647084239170701227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1279555451115942243739877 239916647084239170701227)
                      ·
                        rfl

theorem cell23_467236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_467236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467236 prefixEnd_467236 := by exact prefixLift 467236
  have htrace : WordTrace (prefixWord ++ tailWord_467236) baseStart_467236 baseEnd_467236 := by
    simpa [prefixWord, tailWord_467236, baseEnd_467236] using wordTrace_append hprefix tailTrace_467236
  have hstable : (prefixWord ++ tailWord_467236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467236).length < 2 ^ (prefixWord ++ tailWord_467236).sum := by decide
  have hdescent : baseEnd_467236 < baseStart_467236 := by decide
  rcases family_descends (prefixWord ++ tailWord_467236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467246 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_467246 : Nat := 118140960795 + 467246 * 2 ^ 59
def prefixEnd_467246 : Nat := 4983230072969 + 3 ^ 40 * 467246 * 2
def baseEnd_467246 : Nat := 79973927296928043858727

theorem tailTrace_467246 : CollatzResearch.WordTrace tailWord_467246 prefixEnd_467246 79973927296928043858727 := by
  unfold tailWord_467246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130232708156877013595699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11361241110170010739177061 2130232708156877013595699)
  ·
    refine ⟨3195349062235315520393549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130232708156877013595699 3195349062235315520393549)
    ·
      refine ⟨1198255898338243320147581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3195349062235315520393549 1198255898338243320147581)
      ·
        refine ⟨449345961876841245055343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198255898338243320147581 449345961876841245055343)
        ·
          refine ⟨674018942815261867583015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449345961876841245055343 674018942815261867583015)
          ·
            refine ⟨1011028414222892801374523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674018942815261867583015 1011028414222892801374523)
            ·
              refine ⟨1516542621334339202061785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011028414222892801374523 1516542621334339202061785)
              ·
                refine ⟨1137406966000754401546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516542621334339202061785 1137406966000754401546339)
                ·
                  refine ⟨1706110449001131602319509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137406966000754401546339 1706110449001131602319509)
                  ·
                    refine ⟨79973927296928043858727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1706110449001131602319509 79973927296928043858727)
                    ·
                      rfl

theorem cell23_467246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_467246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467246 prefixEnd_467246 := by exact prefixLift 467246
  have htrace : WordTrace (prefixWord ++ tailWord_467246) baseStart_467246 baseEnd_467246 := by
    simpa [prefixWord, tailWord_467246, baseEnd_467246] using wordTrace_append hprefix tailTrace_467246
  have hstable : (prefixWord ++ tailWord_467246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467246).length < 2 ^ (prefixWord ++ tailWord_467246).sum := by decide
  have hdescent : baseEnd_467246 < baseStart_467246 := by decide
  rcases family_descends (prefixWord ++ tailWord_467246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467249 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_467249 : Nat := 118140960795 + 467249 * 2 ^ 59
def prefixEnd_467249 : Nat := 4983230072969 + 3 ^ 40 * 467249 * 2
def baseEnd_467249 : Nat := 239923322332747619838667

theorem tailTrace_467249 : CollatzResearch.WordTrace tailWord_467249 prefixEnd_467249 239923322332747619838667 := by
  unfold tailWord_467249
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041971084244147621124801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11361314056162765080749867 17041971084244147621124801)
  ·
    refine ⟨12781478313183110715843601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17041971084244147621124801 12781478313183110715843601)
    ·
      refine ⟨9586108734887333036882701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12781478313183110715843601 9586108734887333036882701)
      ·
        refine ⟨3594790775582749888831013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9586108734887333036882701 3594790775582749888831013)
        ·
          refine ⟨674023270421765604155815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3594790775582749888831013 674023270421765604155815)
          ·
            refine ⟨1011034905632648406233723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674023270421765604155815 1011034905632648406233723)
            ·
              refine ⟨1516552358448972609350585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011034905632648406233723 1516552358448972609350585)
              ·
                refine ⟨1137414268836729457012939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516552358448972609350585 1137414268836729457012939)
                ·
                  refine ⟨1706121403255094185519409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137414268836729457012939 1706121403255094185519409)
                  ·
                    refine ⟨1279591052441320639139557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1706121403255094185519409 1279591052441320639139557)
                    ·
                      refine ⟨239923322332747619838667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1279591052441320639139557 239923322332747619838667)
                      ·
                        rfl

theorem cell23_467249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_467249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467249 prefixEnd_467249 := by exact prefixLift 467249
  have htrace : WordTrace (prefixWord ++ tailWord_467249) baseStart_467249 baseEnd_467249 := by
    simpa [prefixWord, tailWord_467249, baseEnd_467249] using wordTrace_append hprefix tailTrace_467249
  have hstable : (prefixWord ++ tailWord_467249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467249).length < 2 ^ (prefixWord ++ tailWord_467249).sum := by decide
  have hdescent : baseEnd_467249 < baseStart_467249 := by decide
  rcases family_descends (prefixWord ++ tailWord_467249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467253 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_467253 : Nat := 118140960795 + 467253 * 2 ^ 59
def prefixEnd_467253 : Nat := 4983230072969 + 3 ^ 40 * 467253 * 2
def baseEnd_467253 : Nat := 239925376255365604188649

theorem tailTrace_467253 : CollatzResearch.WordTrace tailWord_467253 prefixEnd_467253 239925376255365604188649 := by
  unfold tailWord_467253
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042116976229656304270413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11361411317486437536180275 17042116976229656304270413)
  ·
    refine ⟨6390793866086121114101405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17042116976229656304270413 6390793866086121114101405)
    ·
      refine ⟨2396547699782295417788027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6390793866086121114101405 2396547699782295417788027)
      ·
        refine ⟨3594821549673443126682041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396547699782295417788027 3594821549673443126682041)
        ·
          refine ⟨2696116162255082345011531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3594821549673443126682041 2696116162255082345011531)
          ·
            refine ⟨4044174243382623517517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696116162255082345011531 4044174243382623517517297)
            ·
              refine ⟨3033130682536967638137973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044174243382623517517297 3033130682536967638137973)
              ·
                refine ⟨284356001487840716075435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3033130682536967638137973 284356001487840716075435)
                ·
                  refine ⟨426534002231761074113153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284356001487840716075435 426534002231761074113153)
                  ·
                    refine ⟨319900501673820805584865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 426534002231761074113153 319900501673820805584865)
                    ·
                      refine ⟨239925376255365604188649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 319900501673820805584865 239925376255365604188649)
                      ·
                        rfl

theorem cell23_467253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_467253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467253 prefixEnd_467253 := by exact prefixLift 467253
  have htrace : WordTrace (prefixWord ++ tailWord_467253) baseStart_467253 baseEnd_467253 := by
    simpa [prefixWord, tailWord_467253, baseEnd_467253] using wordTrace_append hprefix tailTrace_467253
  have hstable : (prefixWord ++ tailWord_467253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467253).length < 2 ^ (prefixWord ++ tailWord_467253).sum := by decide
  have hdescent : baseEnd_467253 < baseStart_467253 := by decide
  rcases family_descends (prefixWord ++ tailWord_467253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467255 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 7]
def baseStart_467255 : Nat := 118140960795 + 467255 * 2 ^ 59
def prefixEnd_467255 : Nat := 4983230072969 + 3 ^ 40 * 467255 * 2
def baseEnd_467255 : Nat := 79975467738891532121213

theorem tailTrace_467255 : CollatzResearch.WordTrace tailWord_467255 prefixEnd_467255 79975467738891532121213 := by
  unfold tailWord_467255
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042189922222410645843219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11361459948148273763895479 17042189922222410645843219)
  ·
    refine ⟨25563284883333615968764829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17042189922222410645843219 25563284883333615968764829)
    ·
      refine ⟨9586231831250105988286811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25563284883333615968764829 9586231831250105988286811)
      ·
        refine ⟨14379347746875158982430217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586231831250105988286811 14379347746875158982430217)
        ·
          refine ⟨10784510810156369236822663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14379347746875158982430217 10784510810156369236822663)
          ·
            refine ⟨16176766215234553855233995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784510810156369236822663 16176766215234553855233995)
            ·
              refine ⟨24265149322851830782850993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16176766215234553855233995 24265149322851830782850993)
              ·
                refine ⟨18198861992138873087138245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24265149322851830782850993 18198861992138873087138245)
                ·
                  refine ⟨3412286623526038703838421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18198861992138873087138245 3412286623526038703838421)
                  ·
                    refine ⟨79975467738891532121213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3412286623526038703838421 79975467738891532121213)
                    ·
                      rfl

theorem cell23_467255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_467255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467255 prefixEnd_467255 := by exact prefixLift 467255
  have htrace : WordTrace (prefixWord ++ tailWord_467255) baseStart_467255 baseEnd_467255 := by
    simpa [prefixWord, tailWord_467255, baseEnd_467255] using wordTrace_append hprefix tailTrace_467255
  have hstable : (prefixWord ++ tailWord_467255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467255).length < 2 ^ (prefixWord ++ tailWord_467255).sum := by decide
  have hdescent : baseEnd_467255 < baseStart_467255 := by decide
  rcases family_descends (prefixWord ++ tailWord_467255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467372 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_467372 : Nat := 118140960795 + 467372 * 2 ^ 59
def prefixEnd_467372 : Nat := 4983230072969 + 3 ^ 40 * 467372 * 2
def baseEnd_467372 : Nat := 239986480453250638600601

theorem tailTrace_467372 : CollatzResearch.WordTrace tailWord_467372 prefixEnd_467372 239986480453250638600601 := by
  unfold tailWord_467372
  simp only [CollatzResearch.WordTrace]
  refine ⟨8523228631399269813926185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11364304841865693085234913 8523228631399269813926185)
  ·
    refine ⟨6392421473549452360444639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8523228631399269813926185 6392421473549452360444639)
    ·
      refine ⟨9588632210324178540666959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392421473549452360444639 9588632210324178540666959)
      ·
        refine ⟨14382948315486267811000439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588632210324178540666959 14382948315486267811000439)
        ·
          refine ⟨21574422473229401716500659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382948315486267811000439 21574422473229401716500659)
          ·
            refine ⟨32361633709844102574750989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21574422473229401716500659 32361633709844102574750989)
            ·
              refine ⟨12135612641191538465531621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32361633709844102574750989 12135612641191538465531621)
              ·
                refine ⟨2275427370223413462287179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12135612641191538465531621 2275427370223413462287179)
                ·
                  refine ⟨3413141055335120193430769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275427370223413462287179 3413141055335120193430769)
                  ·
                    refine ⟨2559855791501340145073077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413141055335120193430769 2559855791501340145073077)
                    ·
                      refine ⟨239986480453250638600601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2559855791501340145073077 239986480453250638600601)
                      ·
                        rfl

theorem cell23_467372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_467372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467372 prefixEnd_467372 := by exact prefixLift 467372
  have htrace : WordTrace (prefixWord ++ tailWord_467372) baseStart_467372 baseEnd_467372 := by
    simpa [prefixWord, tailWord_467372, baseEnd_467372] using wordTrace_append hprefix tailTrace_467372
  have hstable : (prefixWord ++ tailWord_467372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467372).length < 2 ^ (prefixWord ++ tailWord_467372).sum := by decide
  have hdescent : baseEnd_467372 < baseStart_467372 := by decide
  rcases family_descends (prefixWord ++ tailWord_467372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467389 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_467389 : Nat := 118140960795 + 467389 * 2 ^ 59
def prefixEnd_467389 : Nat := 4983230072969 + 3 ^ 40 * 467389 * 2
def baseEnd_467389 : Nat := 239995209624377072088023

theorem tailTrace_467389 : CollatzResearch.WordTrace tailWord_467389 prefixEnd_467389 239995209624377072088023 := by
  unfold tailWord_467389
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047077303736951531221221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11364718202491301020814147 17047077303736951531221221)
  ·
    refine ⟨3196326994450678412103979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17047077303736951531221221 3196326994450678412103979)
    ·
      refine ⟨4794490491676017618155969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196326994450678412103979 4794490491676017618155969)
      ·
        refine ⟨3595867868757013213616977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794490491676017618155969 3595867868757013213616977)
        ·
          refine ⟨2696900901567759910212733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3595867868757013213616977 2696900901567759910212733)
          ·
            refine ⟨1011337838087909966329775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2696900901567759910212733 1011337838087909966329775)
            ·
              refine ⟨1517006757131864949494663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011337838087909966329775 1517006757131864949494663)
              ·
                refine ⟨2275510135697797424241995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517006757131864949494663 2275510135697797424241995)
                ·
                  refine ⟨3413265203546696136362993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275510135697797424241995 3413265203546696136362993)
                  ·
                    refine ⟨2559948902660022102272245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3413265203546696136362993 2559948902660022102272245)
                    ·
                      refine ⟨239995209624377072088023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2559948902660022102272245 239995209624377072088023)
                      ·
                        rfl

theorem cell23_467389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_467389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467389 prefixEnd_467389 := by exact prefixLift 467389
  have htrace : WordTrace (prefixWord ++ tailWord_467389) baseStart_467389 baseEnd_467389 := by
    simpa [prefixWord, tailWord_467389, baseEnd_467389] using wordTrace_append hprefix tailTrace_467389
  have hstable : (prefixWord ++ tailWord_467389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467389).length < 2 ^ (prefixWord ++ tailWord_467389).sum := by decide
  have hdescent : baseEnd_467389 < baseStart_467389 := by decide
  rcases family_descends (prefixWord ++ tailWord_467389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467409 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_467409 : Nat := 118140960795 + 467409 * 2 ^ 59
def prefixEnd_467409 : Nat := 4983230072969 + 3 ^ 40 * 467409 * 2
def baseEnd_467409 : Nat := 80001826412488997945977

theorem tailTrace_467409 : CollatzResearch.WordTrace tailWord_467409 prefixEnd_467409 80001826412488997945977 := by
  unfold tailWord_467409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047806763664494946949281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11365204509109663297966187 17047806763664494946949281)
  ·
    refine ⟨12785855072748371210211961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17047806763664494946949281 12785855072748371210211961)
    ·
      refine ⟨9589391304561278407658971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12785855072748371210211961 9589391304561278407658971)
      ·
        refine ⟨14384086956841917611488457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9589391304561278407658971 14384086956841917611488457)
        ·
          refine ⟨10788065217631438208616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14384086956841917611488457 10788065217631438208616343)
          ·
            refine ⟨16182097826447157312924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10788065217631438208616343 16182097826447157312924515)
            ·
              refine ⟨24273146739670735969386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16182097826447157312924515 24273146739670735969386773)
              ·
                refine ⟨1137803753422065748565005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24273146739670735969386773 1137803753422065748565005)
                ·
                  refine ⟨426676407533274655711877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137803753422065748565005 426676407533274655711877)
                  ·
                    refine ⟨80001826412488997945977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426676407533274655711877 80001826412488997945977)
                    ·
                      rfl

theorem cell23_467409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_467409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467409 prefixEnd_467409 := by exact prefixLift 467409
  have htrace : WordTrace (prefixWord ++ tailWord_467409) baseStart_467409 baseEnd_467409 := by
    simpa [prefixWord, tailWord_467409, baseEnd_467409] using wordTrace_append hprefix tailTrace_467409
  have hstable : (prefixWord ++ tailWord_467409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467409).length < 2 ^ (prefixWord ++ tailWord_467409).sum := by decide
  have hdescent : baseEnd_467409 < baseStart_467409 := by decide
  rcases family_descends (prefixWord ++ tailWord_467409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467472 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_467472 : Nat := 118140960795 + 467472 * 2 ^ 59
def prefixEnd_467472 : Nat := 4983230072969 + 3 ^ 40 * 467472 * 2
def baseEnd_467472 : Nat := 240037828518700247350141

theorem tailTrace_467472 : CollatzResearch.WordTrace tailWord_467472 prefixEnd_467472 240037828518700247350141 := by
  unfold tailWord_467472
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525052281218128353246335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11366736374957504470995113 8525052281218128353246335)
  ·
    refine ⟨12787578421827192529869503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8525052281218128353246335 12787578421827192529869503)
    ·
      refine ⟨19181367632740788794804255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12787578421827192529869503 19181367632740788794804255)
      ·
        refine ⟨28772051449111183192206383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19181367632740788794804255 28772051449111183192206383)
        ·
          refine ⟨43158077173666774788309575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28772051449111183192206383 43158077173666774788309575)
          ·
            refine ⟨64737115760500162182464363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43158077173666774788309575 64737115760500162182464363)
            ·
              refine ⟨97105673640750243273696545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64737115760500162182464363 97105673640750243273696545)
              ·
                refine ⟨72829255230562682455272409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97105673640750243273696545 72829255230562682455272409)
                ·
                  refine ⟨54621941422922011841454307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72829255230562682455272409 54621941422922011841454307)
                  ·
                    refine ⟨81932912134383017762181461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54621941422922011841454307 81932912134383017762181461)
                    ·
                      refine ⟨240037828518700247350141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 81932912134383017762181461 240037828518700247350141)
                      ·
                        rfl

theorem cell23_467472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_467472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467472 prefixEnd_467472 := by exact prefixLift 467472
  have htrace : WordTrace (prefixWord ++ tailWord_467472) baseStart_467472 baseEnd_467472 := by
    simpa [prefixWord, tailWord_467472, baseEnd_467472] using wordTrace_append hprefix tailTrace_467472
  have hstable : (prefixWord ++ tailWord_467472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467472).length < 2 ^ (prefixWord ++ tailWord_467472).sum := by decide
  have hdescent : baseEnd_467472 < baseStart_467472 := by decide
  rcases family_descends (prefixWord ++ tailWord_467472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467516 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_467516 : Nat := 118140960795 + 467516 * 2 ^ 59
def prefixEnd_467516 : Nat := 4983230072969 + 3 ^ 40 * 467516 * 2
def baseEnd_467516 : Nat := 80020140555832691733313

theorem tailTrace_467516 : CollatzResearch.WordTrace tailWord_467516 prefixEnd_467516 80020140555832691733313 := by
  unfold tailWord_467516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525854687138426110547201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11367806249517901480729601 8525854687138426110547201)
  ·
    refine ⟨6394391015353819582910401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8525854687138426110547201 6394391015353819582910401)
    ·
      refine ⟨4795793261515364687182801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6394391015353819582910401 4795793261515364687182801)
      ·
        refine ⟨3596844946136523515387101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4795793261515364687182801 3596844946136523515387101)
        ·
          refine ⟨1348816854801196318270163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3596844946136523515387101 1348816854801196318270163)
          ·
            refine ⟨2023225282201794477405245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348816854801196318270163 2023225282201794477405245)
            ·
              refine ⟨758709480825672929026967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2023225282201794477405245 758709480825672929026967)
              ·
                refine ⟨1138064221238509393540451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758709480825672929026967 1138064221238509393540451)
                ·
                  refine ⟨1707096331857764090310677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1138064221238509393540451 1707096331857764090310677)
                  ·
                    refine ⟨80020140555832691733313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1707096331857764090310677 80020140555832691733313)
                    ·
                      rfl

theorem cell23_467516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_467516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467516 prefixEnd_467516 := by exact prefixLift 467516
  have htrace : WordTrace (prefixWord ++ tailWord_467516) baseStart_467516 baseEnd_467516 := by
    simpa [prefixWord, tailWord_467516, baseEnd_467516] using wordTrace_append hprefix tailTrace_467516
  have hstable : (prefixWord ++ tailWord_467516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467516).length < 2 ^ (prefixWord ++ tailWord_467516).sum := by decide
  have hdescent : baseEnd_467516 < baseStart_467516 := by decide
  rcases family_descends (prefixWord ++ tailWord_467516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467519 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_467519 : Nat := 118140960795 + 467519 * 2 ^ 59
def prefixEnd_467519 : Nat := 4983230072969 + 3 ^ 40 * 467519 * 2
def baseEnd_467519 : Nat := 240061962109461563462425

theorem tailTrace_467519 : CollatzResearch.WordTrace tailWord_467519 prefixEnd_467519 240061962109461563462425 := by
  unfold tailWord_467519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051818793265983733453611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11367879195510655822302407 17051818793265983733453611)
  ·
    refine ⟨25577728189898975600180417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17051818793265983733453611 25577728189898975600180417)
    ·
      refine ⟨19183296142424231700135313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25577728189898975600180417 19183296142424231700135313)
      ·
        refine ⟨14387472106818173775101485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19183296142424231700135313 14387472106818173775101485)
        ·
          refine ⟨5395302040056815165663057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14387472106818173775101485 5395302040056815165663057)
          ·
            refine ⟨4046476530042611374247293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395302040056815165663057 4046476530042611374247293)
            ·
              refine ⟨1517428698765979265342735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4046476530042611374247293 1517428698765979265342735)
              ·
                refine ⟨2276143048148968898014103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517428698765979265342735 2276143048148968898014103)
                ·
                  refine ⟨3414214572223453347021155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276143048148968898014103 3414214572223453347021155)
                  ·
                    refine ⟨5121321858335180020531733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3414214572223453347021155 5121321858335180020531733)
                    ·
                      refine ⟨240061962109461563462425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5121321858335180020531733 240061962109461563462425)
                      ·
                        rfl

theorem cell23_467519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_467519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467519 prefixEnd_467519 := by exact prefixLift 467519
  have htrace : WordTrace (prefixWord ++ tailWord_467519) baseStart_467519 baseEnd_467519 := by
    simpa [prefixWord, tailWord_467519, baseEnd_467519] using wordTrace_append hprefix tailTrace_467519
  have hstable : (prefixWord ++ tailWord_467519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467519).length < 2 ^ (prefixWord ++ tailWord_467519).sum := by decide
  have hdescent : baseEnd_467519 < baseStart_467519 := by decide
  rcases family_descends (prefixWord ++ tailWord_467519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467533 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_467533 : Nat := 118140960795 + 467533 * 2 ^ 59
def prefixEnd_467533 : Nat := 4983230072969 + 3 ^ 40 * 467533 * 2
def baseEnd_467533 : Nat := 80023050279541502895787

theorem tailTrace_467533 : CollatzResearch.WordTrace tailWord_467533 prefixEnd_467533 80023050279541502895787 := by
  unfold tailWord_467533
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052329415215264124463253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368219610143509416308835 17052329415215264124463253)
  ·
    refine ⟨799327941338215505834215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17052329415215264124463253 799327941338215505834215)
    ·
      refine ⟨1198991912007323258751323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799327941338215505834215 1198991912007323258751323)
      ·
        refine ⟨1798487868010984888126985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198991912007323258751323 1798487868010984888126985)
        ·
          refine ⟨1348865901008238666095239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798487868010984888126985 1348865901008238666095239)
          ·
            refine ⟨2023298851512357999142859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348865901008238666095239 2023298851512357999142859)
            ·
              refine ⟨3034948277268536998714289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023298851512357999142859 3034948277268536998714289)
              ·
                refine ⟨2276211207951402749035717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034948277268536998714289 2276211207951402749035717)
                ·
                  refine ⟨426789601490888015444197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276211207951402749035717 426789601490888015444197)
                  ·
                    refine ⟨80023050279541502895787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426789601490888015444197 80023050279541502895787)
                    ·
                      rfl

theorem cell23_467533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_467533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467533 prefixEnd_467533 := by exact prefixLift 467533
  have htrace : WordTrace (prefixWord ++ tailWord_467533) baseStart_467533 baseEnd_467533 := by
    simpa [prefixWord, tailWord_467533, baseEnd_467533] using wordTrace_append hprefix tailTrace_467533
  have hstable : (prefixWord ++ tailWord_467533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467533).length < 2 ^ (prefixWord ++ tailWord_467533).sum := by decide
  have hdescent : baseEnd_467533 < baseStart_467533 := by decide
  rcases family_descends (prefixWord ++ tailWord_467533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467557 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_467557 : Nat := 118140960795 + 467557 * 2 ^ 59
def prefixEnd_467557 : Nat := 4983230072969 + 3 ^ 40 * 467557 * 2
def baseEnd_467557 : Nat := 240081474374332414787251

theorem tailTrace_467557 : CollatzResearch.WordTrace tailWord_467557 prefixEnd_467557 240081474374332414787251 := by
  unfold tailWord_467557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053204767128316223336925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368803178085544148891283 17053204767128316223336925)
  ·
    refine ⟨6394951787673118583751347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17053204767128316223336925 6394951787673118583751347)
    ·
      refine ⟨9592427681509677875627021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394951787673118583751347 9592427681509677875627021)
      ·
        refine ⟨3597160380566129203360133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9592427681509677875627021 3597160380566129203360133)
        ·
          refine ⟨674467571356149225630025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3597160380566129203360133 674467571356149225630025)
          ·
            refine ⟨505850678517111919222519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674467571356149225630025 505850678517111919222519)
            ·
              refine ⟨758776017775667878833779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505850678517111919222519 758776017775667878833779)
              ·
                refine ⟨1138164026663501818250669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758776017775667878833779 1138164026663501818250669)
                ·
                  refine ⟨426811509998813181844001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138164026663501818250669 426811509998813181844001)
                  ·
                    refine ⟨320108632499109886383001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 426811509998813181844001 320108632499109886383001)
                    ·
                      refine ⟨240081474374332414787251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320108632499109886383001 240081474374332414787251)
                      ·
                        rfl

theorem cell23_467557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_467557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467557 prefixEnd_467557 := by exact prefixLift 467557
  have htrace : WordTrace (prefixWord ++ tailWord_467557) baseStart_467557 baseEnd_467557 := by
    simpa [prefixWord, tailWord_467557, baseEnd_467557] using wordTrace_append hprefix tailTrace_467557
  have hstable : (prefixWord ++ tailWord_467557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467557).length < 2 ^ (prefixWord ++ tailWord_467557).sum := by decide
  have hdescent : baseEnd_467557 < baseStart_467557 := by decide
  rcases family_descends (prefixWord ++ tailWord_467557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467559 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 7]
def baseStart_467559 : Nat := 118140960795 + 467559 * 2 ^ 59
def prefixEnd_467559 : Nat := 4983230072969 + 3 ^ 40 * 467559 * 2
def baseEnd_467559 : Nat := 80027500445213802320747

theorem tailTrace_467559 : CollatzResearch.WordTrace tailWord_467559 prefixEnd_467559 80027500445213802320747 := by
  unfold tailWord_467559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053277713121070564909731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368851808747380376606487 17053277713121070564909731)
  ·
    refine ⟨25579916569681605847364597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053277713121070564909731 25579916569681605847364597)
    ·
      refine ⟨2398117178407650548190431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25579916569681605847364597 2398117178407650548190431)
      ·
        refine ⟨3597175767611475822285647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398117178407650548190431 3597175767611475822285647)
        ·
          refine ⟨5395763651417213733428471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597175767611475822285647 5395763651417213733428471)
          ·
            refine ⟨8093645477125820600142707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395763651417213733428471 8093645477125820600142707)
            ·
              refine ⟨12140468215688730900214061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093645477125820600142707 12140468215688730900214061)
              ·
                refine ⟨4552675580883274087580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12140468215688730900214061 4552675580883274087580273)
                ·
                  refine ⟨3414506685662455565685205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4552675580883274087580273 3414506685662455565685205)
                  ·
                    refine ⟨80027500445213802320747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3414506685662455565685205 80027500445213802320747)
                    ·
                      rfl

theorem cell23_467559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_467559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467559 prefixEnd_467559 := by exact prefixLift 467559
  have htrace : WordTrace (prefixWord ++ tailWord_467559) baseStart_467559 baseEnd_467559 := by
    simpa [prefixWord, tailWord_467559, baseEnd_467559] using wordTrace_append hprefix tailTrace_467559
  have hstable : (prefixWord ++ tailWord_467559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467559).length < 2 ^ (prefixWord ++ tailWord_467559).sum := by decide
  have hdescent : baseEnd_467559 < baseStart_467559 := by decide
  rcases family_descends (prefixWord ++ tailWord_467559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467579 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_467579 : Nat := 118140960795 + 467579 * 2 ^ 59
def prefixEnd_467579 : Nat := 4983230072969 + 3 ^ 40 * 467579 * 2
def baseEnd_467579 : Nat := 240092770948731328712149

theorem tailTrace_467579 : CollatzResearch.WordTrace tailWord_467579 prefixEnd_467579 240092770948731328712149 := by
  unfold tailWord_467579
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054007173048613980637791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11369338115365742653758527 17054007173048613980637791)
  ·
    refine ⟨25581010759572920970956687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17054007173048613980637791 25581010759572920970956687)
    ·
      refine ⟨38371516139359381456435031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25581010759572920970956687 38371516139359381456435031)
      ·
        refine ⟨57557274209039072184652547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38371516139359381456435031 57557274209039072184652547)
        ·
          refine ⟨86335911313558608276978821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57557274209039072184652547 86335911313558608276978821)
          ·
            refine ⟨16187983371292239051933529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86335911313558608276978821 16187983371292239051933529)
            ·
              refine ⟨12140987528469179288950147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16187983371292239051933529 12140987528469179288950147)
              ·
                refine ⟨18211481292703768933425221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12140987528469179288950147 18211481292703768933425221)
                ·
                  refine ⟨3414652742381956675017229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18211481292703768933425221 3414652742381956675017229)
                  ·
                    refine ⟨1280494778393233753131461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414652742381956675017229 1280494778393233753131461)
                    ·
                      refine ⟨240092770948731328712149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1280494778393233753131461 240092770948731328712149)
                      ·
                        rfl

theorem cell23_467579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_467579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467579 prefixEnd_467579 := by exact prefixLift 467579
  have htrace : WordTrace (prefixWord ++ tailWord_467579) baseStart_467579 baseEnd_467579 := by
    simpa [prefixWord, tailWord_467579, baseEnd_467579] using wordTrace_append hprefix tailTrace_467579
  have hstable : (prefixWord ++ tailWord_467579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467579).length < 2 ^ (prefixWord ++ tailWord_467579).sum := by decide
  have hdescent : baseEnd_467579 < baseStart_467579 := by decide
  rcases family_descends (prefixWord ++ tailWord_467579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467583 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 1, 3, 2]
def baseStart_467583 : Nat := 118140960795 + 467583 * 2 ^ 59
def prefixEnd_467583 : Nat := 4983230072969 + 3 ^ 40 * 467583 * 2
def baseEnd_467583 : Nat := 240094824871349313062131

theorem tailTrace_467583 : CollatzResearch.WordTrace tailWord_467583 prefixEnd_467583 240094824871349313062131 := by
  unfold tailWord_467583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054153065034122663783403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11369435376689415109188935 17054153065034122663783403)
  ·
    refine ⟨25581229597551183995675105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17054153065034122663783403 25581229597551183995675105)
    ·
      refine ⟨19185922198163387996756329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25581229597551183995675105 19185922198163387996756329)
      ·
        refine ⟨14389441648622540997567247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19185922198163387996756329 14389441648622540997567247)
        ·
          refine ⟨21584162472933811496350871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14389441648622540997567247 21584162472933811496350871)
          ·
            refine ⟨32376243709400717244526307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21584162472933811496350871 32376243709400717244526307)
            ·
              refine ⟨48564365564101075866789461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32376243709400717244526307 48564365564101075866789461)
              ·
                refine ⟨569113658954309482813939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 48564365564101075866789461 569113658954309482813939)
                ·
                  refine ⟨853670488431464224220909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569113658954309482813939 853670488431464224220909)
                  ·
                    refine ⟨320126433161799084082841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 853670488431464224220909 320126433161799084082841)
                    ·
                      refine ⟨240094824871349313062131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320126433161799084082841 240094824871349313062131)
                      ·
                        rfl

theorem cell23_467583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_467583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467583 prefixEnd_467583 := by exact prefixLift 467583
  have htrace : WordTrace (prefixWord ++ tailWord_467583) baseStart_467583 baseEnd_467583 := by
    simpa [prefixWord, tailWord_467583, baseEnd_467583] using wordTrace_append hprefix tailTrace_467583
  have hstable : (prefixWord ++ tailWord_467583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467583).length < 2 ^ (prefixWord ++ tailWord_467583).sum := by decide
  have hdescent : baseEnd_467583 < baseStart_467583 := by decide
  rcases family_descends (prefixWord ++ tailWord_467583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467743 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 6]
def baseStart_467743 : Nat := 118140960795 + 467743 * 2 ^ 59
def prefixEnd_467743 : Nat := 4983230072969 + 3 ^ 40 * 467743 * 2
def baseEnd_467743 : Nat := 26686331308452076340155

theorem tailTrace_467743 : CollatzResearch.WordTrace tailWord_467743 prefixEnd_467743 26686331308452076340155 := by
  unfold tailWord_467743
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059988744454469989607883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11373325829636313326405255 17059988744454469989607883)
  ·
    refine ⟨25589983116681704984411825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059988744454469989607883 25589983116681704984411825)
    ·
      refine ⟨19192487337511278738308869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589983116681704984411825 19192487337511278738308869)
      ·
        refine ⟨3598591375783364763432913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19192487337511278738308869 3598591375783364763432913)
        ·
          refine ⟨2698943531837523572574685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598591375783364763432913 2698943531837523572574685)
          ·
            refine ⟨1012103824439071339715507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2698943531837523572574685 1012103824439071339715507)
            ·
              refine ⟨1518155736658607009573261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012103824439071339715507 1518155736658607009573261)
              ·
                refine ⟨569308401246977628589973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1518155736658607009573261 569308401246977628589973)
                ·
                  refine ⟨26686331308452076340155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569308401246977628589973 26686331308452076340155)
                  ·
                    rfl

theorem cell23_467743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 6].length) (baseStart_467743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467743 prefixEnd_467743 := by exact prefixLift 467743
  have htrace : WordTrace (prefixWord ++ tailWord_467743) baseStart_467743 baseEnd_467743 := by
    simpa [prefixWord, tailWord_467743, baseEnd_467743] using wordTrace_append hprefix tailTrace_467743
  have hstable : (prefixWord ++ tailWord_467743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467743).length < 2 ^ (prefixWord ++ tailWord_467743).sum := by decide
  have hdescent : baseEnd_467743 < baseStart_467743 := by decide
  rcases family_descends (prefixWord ++ tailWord_467743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467777 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 6]
def baseStart_467777 : Nat := 118140960795 + 467777 * 2 ^ 59
def prefixEnd_467777 : Nat := 4983230072969 + 3 ^ 40 * 467777 * 2
def baseEnd_467777 : Nat := 26688271124257950448471

theorem tailTrace_467777 : CollatzResearch.WordTrace tailWord_467777 prefixEnd_467777 26688271124257950448471 := by
  unfold tailWord_467777
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061228826331293796345585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11374152550887529197563723 17061228826331293796345585)
  ·
    refine ⟨12795921619748470347259189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17061228826331293796345585 12795921619748470347259189)
    ·
      refine ⟨1199617651851419095055549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12795921619748470347259189 1199617651851419095055549)
      ·
        refine ⟨449856619444282160645831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1199617651851419095055549 449856619444282160645831)
        ·
          refine ⟨674784929166423240968747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449856619444282160645831 674784929166423240968747)
          ·
            refine ⟨1012177393749634861453121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674784929166423240968747 1012177393749634861453121)
            ·
              refine ⟨759133045312226146089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012177393749634861453121 759133045312226146089841)
              ·
                refine ⟨569349783984169609567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759133045312226146089841 569349783984169609567381)
                ·
                  refine ⟨26688271124257950448471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569349783984169609567381 26688271124257950448471)
                  ·
                    rfl

theorem cell23_467777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_467777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467777 prefixEnd_467777 := by exact prefixLift 467777
  have htrace : WordTrace (prefixWord ++ tailWord_467777) baseStart_467777 baseEnd_467777 := by
    simpa [prefixWord, tailWord_467777, baseEnd_467777] using wordTrace_append hprefix tailTrace_467777
  have hstable : (prefixWord ++ tailWord_467777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467777).length < 2 ^ (prefixWord ++ tailWord_467777).sum := by decide
  have hdescent : baseEnd_467777 < baseStart_467777 := by decide
  rcases family_descends (prefixWord ++ tailWord_467777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467938 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_467938 : Nat := 118140960795 + 467938 * 2 ^ 59
def prefixEnd_467938 : Nat := 4983230072969 + 3 ^ 40 * 467938 * 2
def baseEnd_467938 : Nat := 240277110503695424122999

theorem tailTrace_467938 : CollatzResearch.WordTrace tailWord_467938 prefixEnd_467938 240277110503695424122999 := by
  unfold tailWord_467938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266775244687004573239117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11378067319165345528637645 4266775244687004573239117)
  ·
    refine ⟨1600040716757626714964669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4266775244687004573239117 1600040716757626714964669)
    ·
      refine ⟨600015268784110018111751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1600040716757626714964669 600015268784110018111751)
      ·
        refine ⟨900022903176165027167627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600015268784110018111751 900022903176165027167627)
        ·
          refine ⟨1350034354764247540751441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900022903176165027167627 1350034354764247540751441)
          ·
            refine ⟨1012525766073185655563581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350034354764247540751441 1012525766073185655563581)
            ·
              refine ⟨379697162277444620836343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012525766073185655563581 379697162277444620836343)
              ·
                refine ⟨569545743416166931254515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379697162277444620836343 569545743416166931254515)
                ·
                  refine ⟨854318615124250396881773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569545743416166931254515 854318615124250396881773)
                  ·
                    refine ⟨320369480671593898830665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854318615124250396881773 320369480671593898830665)
                    ·
                      refine ⟨240277110503695424122999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320369480671593898830665 240277110503695424122999)
                      ·
                        rfl

theorem cell23_467938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_467938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_467938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_467938 prefixEnd_467938 := by exact prefixLift 467938
  have htrace : WordTrace (prefixWord ++ tailWord_467938) baseStart_467938 baseEnd_467938 := by
    simpa [prefixWord, tailWord_467938, baseEnd_467938] using wordTrace_append hprefix tailTrace_467938
  have hstable : (prefixWord ++ tailWord_467938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467938).length < 2 ^ (prefixWord ++ tailWord_467938).sum := by decide
  have hdescent : baseEnd_467938 < baseStart_467938 := by decide
  rcases family_descends (prefixWord ++ tailWord_467938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468017 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_468017 : Nat := 118140960795 + 468017 * 2 ^ 59
def prefixEnd_468017 : Nat := 4983230072969 + 3 ^ 40 * 468017 * 2
def baseEnd_468017 : Nat := 80105891825133538345045

theorem tailTrace_468017 : CollatzResearch.WordTrace tailWord_468017 prefixEnd_468017 80105891825133538345045 := by
  unfold tailWord_468017
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069982345461814785082305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11379988230307876523388203 17069982345461814785082305)
  ·
    refine ⟨12802486759096361088811729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17069982345461814785082305 12802486759096361088811729)
    ·
      refine ⟨9601865069322270816608797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12802486759096361088811729 9601865069322270816608797)
      ·
        refine ⟨3600699400995851556228299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9601865069322270816608797 3600699400995851556228299)
        ·
          refine ⟨5401049101493777334342449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600699400995851556228299 5401049101493777334342449)
          ·
            refine ⟨4050786826120333000756837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401049101493777334342449 4050786826120333000756837)
            ·
              refine ⟨759522529897562437641907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4050786826120333000756837 759522529897562437641907)
              ·
                refine ⟨1139283794846343656462861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759522529897562437641907 1139283794846343656462861)
                ·
                  refine ⟨427231423067378871173573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139283794846343656462861 427231423067378871173573)
                  ·
                    refine ⟨80105891825133538345045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427231423067378871173573 80105891825133538345045)
                    ·
                      rfl

theorem cell23_468017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_468017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468017 prefixEnd_468017 := by exact prefixLift 468017
  have htrace : WordTrace (prefixWord ++ tailWord_468017) baseStart_468017 baseEnd_468017 := by
    simpa [prefixWord, tailWord_468017, baseEnd_468017] using wordTrace_append hprefix tailTrace_468017
  have hstable : (prefixWord ++ tailWord_468017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468017).length < 2 ^ (prefixWord ++ tailWord_468017).sum := by decide
  have hdescent : baseEnd_468017 < baseStart_468017 := by decide
  rcases family_descends (prefixWord ++ tailWord_468017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468040 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_468040 : Nat := 118140960795 + 468040 * 2 ^ 59
def prefixEnd_468040 : Nat := 4983230072969 + 3 ^ 40 * 468040 * 2
def baseEnd_468040 : Nat := 240329485530454025047529

theorem tailTrace_468040 : CollatzResearch.WordTrace tailWord_468040 prefixEnd_468040 240329485530454025047529 := by
  unfold tailWord_468040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535410612189244856584787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11380547482918993142113049 8535410612189244856584787)
  ·
    refine ⟨12803115918283867284877181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535410612189244856584787 12803115918283867284877181)
    ·
      refine ⟨4801168469356450231828943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12803115918283867284877181 4801168469356450231828943)
      ·
        refine ⟨7201752704034675347743415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801168469356450231828943 7201752704034675347743415)
        ·
          refine ⟨10802629056052013021615123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201752704034675347743415 10802629056052013021615123)
          ·
            refine ⟨16203943584078019532422685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802629056052013021615123 16203943584078019532422685)
            ·
              refine ⟨6076478844029257324658507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16203943584078019532422685 6076478844029257324658507)
              ·
                refine ⟨9114718266043885986987761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076478844029257324658507 9114718266043885986987761)
                ·
                  refine ⟨6836038699532914490240821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9114718266043885986987761 6836038699532914490240821)
                  ·
                    refine ⟨640878628081210733460077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6836038699532914490240821 640878628081210733460077)
                    ·
                      refine ⟨240329485530454025047529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 640878628081210733460077 240329485530454025047529)
                      ·
                        rfl

theorem cell23_468040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_468040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468040 prefixEnd_468040 := by exact prefixLift 468040
  have htrace : WordTrace (prefixWord ++ tailWord_468040) baseStart_468040 baseEnd_468040 := by
    simpa [prefixWord, tailWord_468040, baseEnd_468040] using wordTrace_append hprefix tailTrace_468040
  have hstable : (prefixWord ++ tailWord_468040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468040).length < 2 ^ (prefixWord ++ tailWord_468040).sum := by decide
  have hdescent : baseEnd_468040 < baseStart_468040 := by decide
  rcases family_descends (prefixWord ++ tailWord_468040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468061 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_468061 : Nat := 118140960795 + 468061 * 2 ^ 59
def prefixEnd_468061 : Nat := 4983230072969 + 3 ^ 40 * 468061 * 2
def baseEnd_468061 : Nat := 240340268624198442884933

theorem tailTrace_468061 : CollatzResearch.WordTrace tailWord_468061 prefixEnd_468061 240340268624198442884933 := by
  unfold tailWord_468061
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071587157302410299684037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11381058104868273533122691 17071587157302410299684037)
  ·
    refine ⟨3200922591994201931190757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17071587157302410299684037 3200922591994201931190757)
    ·
      refine ⟨600172985998912862098267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3200922591994201931190757 600172985998912862098267)
      ·
        refine ⟨900259478998369293147401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600172985998912862098267 900259478998369293147401)
        ·
          refine ⟨675194609248776969860551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 900259478998369293147401 675194609248776969860551)
          ·
            refine ⟨1012791913873165454790827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675194609248776969860551 1012791913873165454790827)
            ·
              refine ⟨1519187870809748182186241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012791913873165454790827 1519187870809748182186241)
              ·
                refine ⟨1139390903107311136639681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519187870809748182186241 1139390903107311136639681)
                ·
                  refine ⟨854543177330483352479761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139390903107311136639681 854543177330483352479761)
                  ·
                    refine ⟨640907382997862514359821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 854543177330483352479761 640907382997862514359821)
                    ·
                      refine ⟨240340268624198442884933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 640907382997862514359821 240340268624198442884933)
                      ·
                        rfl

theorem cell23_468061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_468061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468061 prefixEnd_468061 := by exact prefixLift 468061
  have htrace : WordTrace (prefixWord ++ tailWord_468061) baseStart_468061 baseEnd_468061 := by
    simpa [prefixWord, tailWord_468061, baseEnd_468061] using wordTrace_append hprefix tailTrace_468061
  have hstable : (prefixWord ++ tailWord_468061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468061).length < 2 ^ (prefixWord ++ tailWord_468061).sum := by decide
  have hdescent : baseEnd_468061 < baseStart_468061 := by decide
  rcases family_descends (prefixWord ++ tailWord_468061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468101 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_468101 : Nat := 118140960795 + 468101 * 2 ^ 59
def prefixEnd_468101 : Nat := 4983230072969 + 3 ^ 40 * 468101 * 2
def baseEnd_468101 : Nat := 240360807850378286384749

theorem tailTrace_468101 : CollatzResearch.WordTrace tailWord_468101 prefixEnd_468101 240360807850378286384749 := by
  unfold tailWord_468101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17073046077157497131140157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11382030718104998087426771 17073046077157497131140157)
  ·
    refine ⟨6402392278934061424177559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17073046077157497131140157 6402392278934061424177559)
    ·
      refine ⟨9603588418401092136266339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402392278934061424177559 9603588418401092136266339)
      ·
        refine ⟨14405382627601638204399509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9603588418401092136266339 14405382627601638204399509)
        ·
          refine ⟨675252310668826790831227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14405382627601638204399509 675252310668826790831227)
          ·
            refine ⟨1012878466003240186246841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675252310668826790831227 1012878466003240186246841)
            ·
              refine ⟨759658849502430139685131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012878466003240186246841 759658849502430139685131)
              ·
                refine ⟨1139488274253645209527697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759658849502430139685131 1139488274253645209527697)
                ·
                  refine ⟨854616205690233907145773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139488274253645209527697 854616205690233907145773)
                  ·
                    refine ⟨320481077133837715179665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 854616205690233907145773 320481077133837715179665)
                    ·
                      refine ⟨240360807850378286384749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320481077133837715179665 240360807850378286384749)
                      ·
                        rfl

theorem cell23_468101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_468101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468101 prefixEnd_468101 := by exact prefixLift 468101
  have htrace : WordTrace (prefixWord ++ tailWord_468101) baseStart_468101 baseEnd_468101 := by
    simpa [prefixWord, tailWord_468101, baseEnd_468101] using wordTrace_append hprefix tailTrace_468101
  have hstable : (prefixWord ++ tailWord_468101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468101).length < 2 ^ (prefixWord ++ tailWord_468101).sum := by decide
  have hdescent : baseEnd_468101 < baseStart_468101 := by decide
  rcases family_descends (prefixWord ++ tailWord_468101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468120 : List Nat := [2, 1, 2, 4, 2, 12]
def baseStart_468120 : Nat := 118140960795 + 468120 * 2 ^ 59
def prefixEnd_468120 : Nat := 4983230072969 + 3 ^ 40 * 468120 * 2
def baseEnd_468120 : Nat := 989179275649439144227

theorem tailTrace_468120 : CollatzResearch.WordTrace tailWord_468120 prefixEnd_468120 989179275649439144227 := by
  unfold tailWord_468120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536869532044331688040907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11382492709392442250721209 8536869532044331688040907)
  ·
    refine ⟨12805304298066497532061361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8536869532044331688040907 12805304298066497532061361)
    ·
      refine ⟨9603978223549873149046021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12805304298066497532061361 9603978223549873149046021)
      ·
        refine ⟨1800745916915601215446129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9603978223549873149046021 1800745916915601215446129)
        ·
          refine ⟨1350559437686700911584597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800745916915601215446129 1350559437686700911584597)
          ·
            refine ⟨989179275649439144227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1350559437686700911584597 989179275649439144227)
            ·
              rfl

theorem cell23_468120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 12].length) (baseStart_468120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468120 prefixEnd_468120 := by exact prefixLift 468120
  have htrace : WordTrace (prefixWord ++ tailWord_468120) baseStart_468120 baseEnd_468120 := by
    simpa [prefixWord, tailWord_468120, baseEnd_468120] using wordTrace_append hprefix tailTrace_468120
  have hstable : (prefixWord ++ tailWord_468120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468120).length < 2 ^ (prefixWord ++ tailWord_468120).sum := by decide
  have hdescent : baseEnd_468120 < baseStart_468120 := by decide
  rcases family_descends (prefixWord ++ tailWord_468120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468124 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_468124 : Nat := 118140960795 + 468124 * 2 ^ 59
def prefixEnd_468124 : Nat := 4983230072969 + 3 ^ 40 * 468124 * 2
def baseEnd_468124 : Nat := 80124205968477232132381

theorem tailTrace_468124 : CollatzResearch.WordTrace tailWord_468124 prefixEnd_468124 80124205968477232132381 := by
  unfold tailWord_468124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536942478037086029613713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11382589970716114706151617 8536942478037086029613713)
  ·
    refine ⟨6402706858527814522210285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8536942478037086029613713 6402706858527814522210285)
    ·
      refine ⟨2401015071947930445828857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6402706858527814522210285 2401015071947930445828857)
      ·
        refine ⟨1800761303960947834371643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2401015071947930445828857 1800761303960947834371643)
        ·
          refine ⟨2701141955941421751557465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800761303960947834371643 2701141955941421751557465)
          ·
            refine ⟨2025856466956066313668099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701141955941421751557465 2025856466956066313668099)
            ·
              refine ⟨3038784700434099470502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025856466956066313668099 3038784700434099470502149)
              ·
                refine ⟨569772131331393650719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3038784700434099470502149 569772131331393650719153)
                ·
                  refine ⟨427329098498545238039365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 569772131331393650719153 427329098498545238039365)
                  ·
                    refine ⟨80124205968477232132381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427329098498545238039365 80124205968477232132381)
                    ·
                      rfl

theorem cell23_468124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_468124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468124 prefixEnd_468124 := by exact prefixLift 468124
  have htrace : WordTrace (prefixWord ++ tailWord_468124) baseStart_468124 baseEnd_468124 := by
    simpa [prefixWord, tailWord_468124, baseEnd_468124] using wordTrace_append hprefix tailTrace_468124
  have hstable : (prefixWord ++ tailWord_468124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468124).length < 2 ^ (prefixWord ++ tailWord_468124).sum := by decide
  have hdescent : baseEnd_468124 < baseStart_468124 := by decide
  rcases family_descends (prefixWord ++ tailWord_468124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468147 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3]
def baseStart_468147 : Nat := 118140960795 + 468147 * 2 ^ 59
def prefixEnd_468147 : Nat := 4983230072969 + 3 ^ 40 * 468147 * 2
def baseEnd_468147 : Nat := 240384427960485106409537

theorem tailTrace_468147 : CollatzResearch.WordTrace tailWord_468147 prefixEnd_468147 240384427960485106409537 := by
  unfold tailWord_468147
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074723834990846987314695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11383149223327231324876463 17074723834990846987314695)
  ·
    refine ⟨25612085752486270480972043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17074723834990846987314695 25612085752486270480972043)
    ·
      refine ⟨38418128628729405721458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25612085752486270480972043 38418128628729405721458065)
      ·
        refine ⟨28813596471547054291093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38418128628729405721458065 28813596471547054291093549)
        ·
          refine ⟨10805098676830145359160081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28813596471547054291093549 10805098676830145359160081)
          ·
            refine ⟨8103824007622609019370061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10805098676830145359160081 8103824007622609019370061)
            ·
              refine ⟨3038934002858478382263773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8103824007622609019370061 3038934002858478382263773)
              ·
                refine ⟨1139600251071929393348915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3038934002858478382263773 1139600251071929393348915)
                ·
                  refine ⟨1709400376607894090023373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139600251071929393348915 1709400376607894090023373)
                  ·
                    refine ⟨641025141227960283758765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1709400376607894090023373 641025141227960283758765)
                    ·
                      refine ⟨240384427960485106409537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641025141227960283758765 240384427960485106409537)
                      ·
                        rfl

theorem cell23_468147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_468147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468147 prefixEnd_468147 := by exact prefixLift 468147
  have htrace : WordTrace (prefixWord ++ tailWord_468147) baseStart_468147 baseEnd_468147 := by
    simpa [prefixWord, tailWord_468147, baseEnd_468147] using wordTrace_append hprefix tailTrace_468147
  have hstable : (prefixWord ++ tailWord_468147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468147).length < 2 ^ (prefixWord ++ tailWord_468147).sum := by decide
  have hdescent : baseEnd_468147 < baseStart_468147 := by decide
  rcases family_descends (prefixWord ++ tailWord_468147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468162 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_468162 : Nat := 118140960795 + 468162 * 2 ^ 59
def prefixEnd_468162 : Nat := 4983230072969 + 3 ^ 40 * 468162 * 2
def baseEnd_468162 : Nat := 80130710056767515907323

theorem tailTrace_468162 : CollatzResearch.WordTrace tailWord_468162 prefixEnd_468162 80130710056767515907323 := by
  unfold tailWord_468162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268817732484126137277685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11383513953291003032740493 4268817732484126137277685)
  ·
    refine ⟨400201662420386825369783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4268817732484126137277685 400201662420386825369783)
    ·
      refine ⟨600302493630580238054675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400201662420386825369783 600302493630580238054675)
      ·
        refine ⟨900453740445870357082013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600302493630580238054675 900453740445870357082013)
        ·
          refine ⟨337670152667201383905755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 900453740445870357082013 337670152667201383905755)
          ·
            refine ⟨506505229000802075858633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337670152667201383905755 506505229000802075858633)
            ·
              refine ⟨379878921750601556893975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506505229000802075858633 379878921750601556893975)
              ·
                refine ⟨569818382625902335340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379878921750601556893975 569818382625902335340963)
                ·
                  refine ⟨854727573938853503011445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569818382625902335340963 854727573938853503011445)
                  ·
                    refine ⟨80130710056767515907323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 854727573938853503011445 80130710056767515907323)
                    ·
                      rfl

theorem cell23_468162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_468162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468162 prefixEnd_468162 := by exact prefixLift 468162
  have htrace : WordTrace (prefixWord ++ tailWord_468162) baseStart_468162 baseEnd_468162 := by
    simpa [prefixWord, tailWord_468162, baseEnd_468162] using wordTrace_append hprefix tailTrace_468162
  have hstable : (prefixWord ++ tailWord_468162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468162).length < 2 ^ (prefixWord ++ tailWord_468162).sum := by decide
  have hdescent : baseEnd_468162 < baseStart_468162 := by decide
  rcases family_descends (prefixWord ++ tailWord_468162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468181 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_468181 : Nat := 118140960795 + 468181 * 2 ^ 59
def prefixEnd_468181 : Nat := 4983230072969 + 3 ^ 40 * 468181 * 2
def baseEnd_468181 : Nat := 240401886302737973384381

theorem tailTrace_468181 : CollatzResearch.WordTrace tailWord_468181 prefixEnd_468181 240401886302737973384381 := by
  unfold tailWord_468181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17075963916867670794052397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11383975944578447196034931 17075963916867670794052397)
  ·
    refine ⟨6403486468825376547769649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17075963916867670794052397 6403486468825376547769649)
    ·
      refine ⟨4802614851619032410827237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6403486468825376547769649 4802614851619032410827237)
      ·
        refine ⟨900490284678568577030107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4802614851619032410827237 900490284678568577030107)
        ·
          refine ⟨1350735427017852865545161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900490284678568577030107 1350735427017852865545161)
          ·
            refine ⟨1013051570263389649158871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350735427017852865545161 1013051570263389649158871)
            ·
              refine ⟨1519577355395084473738307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013051570263389649158871 1519577355395084473738307)
              ·
                refine ⟨2279366033092626710607461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519577355395084473738307 2279366033092626710607461)
                ·
                  refine ⟨427381131204867508238899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279366033092626710607461 427381131204867508238899)
                  ·
                    refine ⟨641071696807301262358349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427381131204867508238899 641071696807301262358349)
                    ·
                      refine ⟨240401886302737973384381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641071696807301262358349 240401886302737973384381)
                      ·
                        rfl

theorem cell23_468181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_468181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468181 prefixEnd_468181 := by exact prefixLift 468181
  have htrace : WordTrace (prefixWord ++ tailWord_468181) baseStart_468181 baseEnd_468181 := by
    simpa [prefixWord, tailWord_468181, baseEnd_468181] using wordTrace_append hprefix tailTrace_468181
  have hstable : (prefixWord ++ tailWord_468181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468181).length < 2 ^ (prefixWord ++ tailWord_468181).sum := by decide
  have hdescent : baseEnd_468181 < baseStart_468181 := by decide
  rcases family_descends (prefixWord ++ tailWord_468181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468257 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_468257 : Nat := 118140960795 + 468257 * 2 ^ 59
def prefixEnd_468257 : Nat := 4983230072969 + 3 ^ 40 * 468257 * 2
def baseEnd_468257 : Nat := 80146970277493225344677

theorem tailTrace_468257 : CollatzResearch.WordTrace tailWord_468257 prefixEnd_468257 80146970277493225344677 := by
  unfold tailWord_468257
  simp only [CollatzResearch.WordTrace]
  refine ⟨17078735864592335773819025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11385823909728223849212683 17078735864592335773819025)
  ·
    refine ⟨12809051898444251830364269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17078735864592335773819025 12809051898444251830364269)
    ·
      refine ⟨4803394461916594436386601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12809051898444251830364269 4803394461916594436386601)
      ·
        refine ⟨3602545846437445827289951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803394461916594436386601 3602545846437445827289951)
        ·
          refine ⟨5403818769656168740934927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602545846437445827289951 5403818769656168740934927)
          ·
            refine ⟨8105728154484253111402391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403818769656168740934927 8105728154484253111402391)
            ·
              refine ⟨12158592231726379667103587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105728154484253111402391 12158592231726379667103587)
              ·
                refine ⟨18237888347589569500655381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158592231726379667103587 18237888347589569500655381)
                ·
                  refine ⟨854901016293261070343221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18237888347589569500655381 854901016293261070343221)
                  ·
                    refine ⟨80146970277493225344677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 854901016293261070343221 80146970277493225344677)
                    ·
                      rfl

theorem cell23_468257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_468257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468257 prefixEnd_468257 := by exact prefixLift 468257
  have htrace : WordTrace (prefixWord ++ tailWord_468257) baseStart_468257 baseEnd_468257 := by
    simpa [prefixWord, tailWord_468257, baseEnd_468257] using wordTrace_append hprefix tailTrace_468257
  have hstable : (prefixWord ++ tailWord_468257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468257).length < 2 ^ (prefixWord ++ tailWord_468257).sum := by decide
  have hdescent : baseEnd_468257 < baseStart_468257 := by decide
  rcases family_descends (prefixWord ++ tailWord_468257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468274 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_468274 : Nat := 118140960795 + 468274 * 2 ^ 59
def prefixEnd_468274 : Nat := 4983230072969 + 3 ^ 40 * 468274 * 2
def baseEnd_468274 : Nat := 80149880001202036507151

theorem tailTrace_468274 : CollatzResearch.WordTrace tailWord_468274 prefixEnd_468274 80149880001202036507151 := by
  unfold tailWord_468274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269838976382686919296969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11386237270353831784791917 4269838976382686919296969)
  ·
    refine ⟨3202379232287015189472727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4269838976382686919296969 3202379232287015189472727)
    ·
      refine ⟨4803568848430522784209091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202379232287015189472727 4803568848430522784209091)
      ·
        refine ⟨7205353272645784176313637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803568848430522784209091 7205353272645784176313637)
        ·
          refine ⟨1351003738621084533058807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7205353272645784176313637 1351003738621084533058807)
          ·
            refine ⟨2026505607931626799588211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351003738621084533058807 2026505607931626799588211)
            ·
              refine ⟨3039758411897440199382317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026505607931626799588211 3039758411897440199382317)
              ·
                refine ⟨1139909404461540074768369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3039758411897440199382317 1139909404461540074768369)
                ·
                  refine ⟨854932053346155056076277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1139909404461540074768369 854932053346155056076277)
                  ·
                    refine ⟨80149880001202036507151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 854932053346155056076277 80149880001202036507151)
                    ·
                      rfl

theorem cell23_468274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_468274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468274 prefixEnd_468274 := by exact prefixLift 468274
  have htrace : WordTrace (prefixWord ++ tailWord_468274) baseStart_468274 baseEnd_468274 := by
    simpa [prefixWord, tailWord_468274, baseEnd_468274] using wordTrace_append hprefix tailTrace_468274
  have hstable : (prefixWord ++ tailWord_468274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468274).length < 2 ^ (prefixWord ++ tailWord_468274).sum := by decide
  have hdescent : baseEnd_468274 < baseStart_468274 := by decide
  rcases family_descends (prefixWord ++ tailWord_468274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468304 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_468304 : Nat := 118140960795 + 468304 * 2 ^ 59
def prefixEnd_468304 : Nat := 4983230072969 + 3 ^ 40 * 468304 * 2
def baseEnd_468304 : Nat := 80155014807746997382105

theorem tailTrace_468304 : CollatzResearch.WordTrace tailWord_468304 prefixEnd_468304 80155014807746997382105 := by
  unfold tailWord_468304
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540225047711031400389983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11386966730281375200519977 8540225047711031400389983)
  ·
    refine ⟨12810337571566547100584975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540225047711031400389983 12810337571566547100584975)
    ·
      refine ⟨19215506357349820650877463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12810337571566547100584975 19215506357349820650877463)
      ·
        refine ⟨28823259536024730976316195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19215506357349820650877463 28823259536024730976316195)
        ·
          refine ⟨43234889304037096464474293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28823259536024730976316195 43234889304037096464474293)
          ·
            refine ⟨4053270872253477793544465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43234889304037096464474293 4053270872253477793544465)
            ·
              refine ⟨3039953154190108345158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053270872253477793544465 3039953154190108345158349)
              ·
                refine ⟨1139982432821290629434381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3039953154190108345158349 1139982432821290629434381)
                ·
                  refine ⟨427493412307983986037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139982432821290629434381 427493412307983986037893)
                  ·
                    refine ⟨80155014807746997382105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427493412307983986037893 80155014807746997382105)
                    ·
                      rfl

theorem cell23_468304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_468304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468304 prefixEnd_468304 := by exact prefixLift 468304
  have htrace : WordTrace (prefixWord ++ tailWord_468304) baseStart_468304 baseEnd_468304 := by
    simpa [prefixWord, tailWord_468304, baseEnd_468304] using wordTrace_append hprefix tailTrace_468304
  have hstable : (prefixWord ++ tailWord_468304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468304).length < 2 ^ (prefixWord ++ tailWord_468304).sum := by decide
  have hdescent : baseEnd_468304 < baseStart_468304 := by decide
  rcases family_descends (prefixWord ++ tailWord_468304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468311 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_468311 : Nat := 118140960795 + 468311 * 2 ^ 59
def prefixEnd_468311 : Nat := 4983230072969 + 3 ^ 40 * 468311 * 2
def baseEnd_468311 : Nat := 240468638787822464758783

theorem tailTrace_468311 : CollatzResearch.WordTrace tailWord_468311 prefixEnd_468311 240468638787822464758783 := by
  unfold tailWord_468311
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080705406396702996284787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11387136937597801997523191 17080705406396702996284787)
  ·
    refine ⟨25621058109595054494427181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17080705406396702996284787 25621058109595054494427181)
    ·
      refine ⟨9607896791098145435410193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25621058109595054494427181 9607896791098145435410193)
      ·
        refine ⟨7205922593323609076557645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607896791098145435410193 7205922593323609076557645)
        ·
          refine ⟨2702220972496353403709117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7205922593323609076557645 2702220972496353403709117)
          ·
            refine ⟨1013332864686132526390919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2702220972496353403709117 1013332864686132526390919)
            ·
              refine ⟨1519999297029198789586379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013332864686132526390919 1519999297029198789586379)
              ·
                refine ⟨2279998945543798184379569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519999297029198789586379 2279998945543798184379569)
                ·
                  refine ⟨1709999209157848638284677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2279998945543798184379569 1709999209157848638284677)
                  ·
                    refine ⟨320624851717096619678377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1709999209157848638284677 320624851717096619678377)
                    ·
                      refine ⟨240468638787822464758783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320624851717096619678377 240468638787822464758783)
                      ·
                        rfl

theorem cell23_468311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_468311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468311 prefixEnd_468311 := by exact prefixLift 468311
  have htrace : WordTrace (prefixWord ++ tailWord_468311) baseStart_468311 baseEnd_468311 := by
    simpa [prefixWord, tailWord_468311, baseEnd_468311] using wordTrace_append hprefix tailTrace_468311
  have hstable : (prefixWord ++ tailWord_468311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468311).length < 2 ^ (prefixWord ++ tailWord_468311).sum := by decide
  have hdescent : baseEnd_468311 < baseStart_468311 := by decide
  rcases family_descends (prefixWord ++ tailWord_468311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468314 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_468314 : Nat := 118140960795 + 468314 * 2 ^ 59
def prefixEnd_468314 : Nat := 4983230072969 + 3 ^ 40 * 468314 * 2
def baseEnd_468314 : Nat := 240470179229785953021269

theorem tailTrace_468314 : CollatzResearch.WordTrace tailWord_468314 prefixEnd_468314 240470179229785953021269 := by
  unfold tailWord_468314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270203706346458627160999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11387209883590556339095997 4270203706346458627160999)
  ·
    refine ⟨6405305559519687940741499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4270203706346458627160999 6405305559519687940741499)
    ·
      refine ⟨9607958339279531911112249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405305559519687940741499 9607958339279531911112249)
      ·
        refine ⟨7205968754459648933334187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607958339279531911112249 7205968754459648933334187)
        ·
          refine ⟨10808953131689473400001281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205968754459648933334187 10808953131689473400001281)
          ·
            refine ⟨8106714848767105050000961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10808953131689473400001281 8106714848767105050000961)
            ·
              refine ⟨6080036136575328787500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8106714848767105050000961 6080036136575328787500721)
              ·
                refine ⟨4560027102431496590625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080036136575328787500721 4560027102431496590625541)
                ·
                  refine ⟨855005081705905610742289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4560027102431496590625541 855005081705905610742289)
                  ·
                    refine ⟨641253811279429208056717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855005081705905610742289 641253811279429208056717)
                    ·
                      refine ⟨240470179229785953021269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641253811279429208056717 240470179229785953021269)
                      ·
                        rfl

theorem cell23_468314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_468314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468314 prefixEnd_468314 := by exact prefixLift 468314
  have htrace : WordTrace (prefixWord ++ tailWord_468314) baseStart_468314 baseEnd_468314 := by
    simpa [prefixWord, tailWord_468314, baseEnd_468314] using wordTrace_append hprefix tailTrace_468314
  have hstable : (prefixWord ++ tailWord_468314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468314).length < 2 ^ (prefixWord ++ tailWord_468314).sum := by decide
  have hdescent : baseEnd_468314 < baseStart_468314 := by decide
  rcases family_descends (prefixWord ++ tailWord_468314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468328 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_468328 : Nat := 118140960795 + 468328 * 2 ^ 59
def prefixEnd_468328 : Nat := 4983230072969 + 3 ^ 40 * 468328 * 2
def baseEnd_468328 : Nat := 240477367958948898246205

theorem tailTrace_468328 : CollatzResearch.WordTrace tailWord_468328 prefixEnd_468328 240477367958948898246205 := by
  unfold tailWord_468328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540662723667557449826819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11387550298223409933102425 8540662723667557449826819)
  ·
    refine ⟨12810994085501336174740229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540662723667557449826819 12810994085501336174740229)
    ·
      refine ⟨2402061391031500532763793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12810994085501336174740229 2402061391031500532763793)
      ·
        refine ⟨1801546043273625399572845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402061391031500532763793 1801546043273625399572845)
        ·
          refine ⟨675579766227609524839817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1801546043273625399572845 675579766227609524839817)
          ·
            refine ⟨506684824670707143629863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675579766227609524839817 506684824670707143629863)
            ·
              refine ⟨760027237006060715444795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506684824670707143629863 760027237006060715444795)
              ·
                refine ⟨1140040855509091073167193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760027237006060715444795 1140040855509091073167193)
                ·
                  refine ⟨855030641631818304875395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1140040855509091073167193 855030641631818304875395)
                  ·
                    refine ⟨1282545962447727457313093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855030641631818304875395 1282545962447727457313093)
                    ·
                      refine ⟨240477367958948898246205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1282545962447727457313093 240477367958948898246205)
                      ·
                        rfl

theorem cell23_468328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_468328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468328 prefixEnd_468328 := by exact prefixLift 468328
  have htrace : WordTrace (prefixWord ++ tailWord_468328) baseStart_468328 baseEnd_468328 := by
    simpa [prefixWord, tailWord_468328, baseEnd_468328] using wordTrace_append hprefix tailTrace_468328
  have hstable : (prefixWord ++ tailWord_468328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468328).length < 2 ^ (prefixWord ++ tailWord_468328).sum := by decide
  have hdescent : baseEnd_468328 < baseStart_468328 := by decide
  rcases family_descends (prefixWord ++ tailWord_468328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468338 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_468338 : Nat := 118140960795 + 468338 * 2 ^ 59
def prefixEnd_468338 : Nat := 4983230072969 + 3 ^ 40 * 468338 * 2
def baseEnd_468338 : Nat := 80160834255164619707053

theorem tailTrace_468338 : CollatzResearch.WordTrace tailWord_468338 prefixEnd_468338 80160834255164619707053 := by
  unfold tailWord_468338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270422544324721651879417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11387793451532591071678445 4270422544324721651879417)
  ·
    refine ⟨3202816908243541238909563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4270422544324721651879417 3202816908243541238909563)
    ·
      refine ⟨4804225362365311858364345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202816908243541238909563 4804225362365311858364345)
      ·
        refine ⟨3603169021773983893773259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804225362365311858364345 3603169021773983893773259)
        ·
          refine ⟨5404753532660975840659889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603169021773983893773259 5404753532660975840659889)
          ·
            refine ⟨4053565149495731880494917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5404753532660975840659889 4053565149495731880494917)
            ·
              refine ⟨760043465530449727592797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4053565149495731880494917 760043465530449727592797)
              ·
                refine ⟨285016299573918647847299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760043465530449727592797 285016299573918647847299)
                ·
                  refine ⟨427524449360877971770949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285016299573918647847299 427524449360877971770949)
                  ·
                    refine ⟨80160834255164619707053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427524449360877971770949 80160834255164619707053)
                    ·
                      rfl

theorem cell23_468338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_468338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468338 prefixEnd_468338 := by exact prefixLift 468338
  have htrace : WordTrace (prefixWord ++ tailWord_468338) baseStart_468338 baseEnd_468338 := by
    simpa [prefixWord, tailWord_468338, baseEnd_468338] using wordTrace_append hprefix tailTrace_468338
  have hstable : (prefixWord ++ tailWord_468338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468338).length < 2 ^ (prefixWord ++ tailWord_468338).sum := by decide
  have hdescent : baseEnd_468338 < baseStart_468338 := by decide
  rcases family_descends (prefixWord ++ tailWord_468338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468381 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_468381 : Nat := 118140960795 + 468381 * 2 ^ 59
def prefixEnd_468381 : Nat := 4983230072969 + 3 ^ 40 * 468381 * 2
def baseEnd_468381 : Nat := 80168194144545730294487

theorem tailTrace_468381 : CollatzResearch.WordTrace tailWord_468381 prefixEnd_468381 80168194144545730294487 := by
  unfold tailWord_468381
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083258516143104951332997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11388839010762069967555331 17083258516143104951332997)
  ·
    refine ⟨3203110971776832178374937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17083258516143104951332997 3203110971776832178374937)
    ·
      refine ⟨2402333228832624133781203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3203110971776832178374937 2402333228832624133781203)
      ·
        refine ⟨3603499843248936200671805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402333228832624133781203 3603499843248936200671805)
        ·
          refine ⟨1351312441218351075251927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3603499843248936200671805 1351312441218351075251927)
          ·
            refine ⟨2026968661827526612877891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351312441218351075251927 2026968661827526612877891)
            ·
              refine ⟨3040452992741289919316837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026968661827526612877891 3040452992741289919316837)
              ·
                refine ⟨570084936138991859871907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3040452992741289919316837 570084936138991859871907)
                ·
                  refine ⟨855127404208487789807861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570084936138991859871907 855127404208487789807861)
                  ·
                    refine ⟨80168194144545730294487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 855127404208487789807861 80168194144545730294487)
                    ·
                      rfl

theorem cell23_468381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_468381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468381 prefixEnd_468381 := by exact prefixLift 468381
  have htrace : WordTrace (prefixWord ++ tailWord_468381) baseStart_468381 baseEnd_468381 := by
    simpa [prefixWord, tailWord_468381, baseEnd_468381] using wordTrace_append hprefix tailTrace_468381
  have hstable : (prefixWord ++ tailWord_468381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468381).length < 2 ^ (prefixWord ++ tailWord_468381).sum := by decide
  have hdescent : baseEnd_468381 < baseStart_468381 := by decide
  rcases family_descends (prefixWord ++ tailWord_468381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468401 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_468401 : Nat := 118140960795 + 468401 * 2 ^ 59
def prefixEnd_468401 : Nat := 4983230072969 + 3 ^ 40 * 468401 * 2
def baseEnd_468401 : Nat := 240514852046727112633369

theorem tailTrace_468401 : CollatzResearch.WordTrace tailWord_468401 prefixEnd_468401 240514852046727112633369 := by
  unfold tailWord_468401
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083987976070648367061057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11389325317380432244707371 17083987976070648367061057)
  ·
    refine ⟨12812990982052986275295793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17083987976070648367061057 12812990982052986275295793)
    ·
      refine ⟨9609743236539739706471845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12812990982052986275295793 9609743236539739706471845)
      ·
        refine ⟨1801826856851201194963471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9609743236539739706471845 1801826856851201194963471)
        ·
          refine ⟨2702740285276801792445207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801826856851201194963471 2702740285276801792445207)
          ·
            refine ⟨4054110427915202688667811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702740285276801792445207 4054110427915202688667811)
            ·
              refine ⟨6081165641872804033001717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054110427915202688667811 6081165641872804033001717)
              ·
                refine ⟨570109278925575378093911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6081165641872804033001717 570109278925575378093911)
                ·
                  refine ⟨855163918388363067140867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570109278925575378093911 855163918388363067140867)
                  ·
                    refine ⟨1282745877582544600711301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 855163918388363067140867 1282745877582544600711301)
                    ·
                      refine ⟨240514852046727112633369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1282745877582544600711301 240514852046727112633369)
                      ·
                        rfl

theorem cell23_468401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_468401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468401 prefixEnd_468401 := by exact prefixLift 468401
  have htrace : WordTrace (prefixWord ++ tailWord_468401) baseStart_468401 baseEnd_468401 := by
    simpa [prefixWord, tailWord_468401, baseEnd_468401] using wordTrace_append hprefix tailTrace_468401
  have hstable : (prefixWord ++ tailWord_468401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468401).length < 2 ^ (prefixWord ++ tailWord_468401).sum := by decide
  have hdescent : baseEnd_468401 < baseStart_468401 := by decide
  rcases family_descends (prefixWord ++ tailWord_468401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468412 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_468412 : Nat := 118140960795 + 468412 * 2 ^ 59
def prefixEnd_468412 : Nat := 4983230072969 + 3 ^ 40 * 468412 * 2
def baseEnd_468412 : Nat := 240520500333926569595819

theorem tailTrace_468412 : CollatzResearch.WordTrace tailWord_468412 prefixEnd_468412 240520500333926569595819 := by
  unfold tailWord_468412
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542194589515398622855745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11389592786020531497140993 8542194589515398622855745)
  ·
    refine ⟨6406645942136548967141809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8542194589515398622855745 6406645942136548967141809)
    ·
      refine ⟨4804984456602411725356357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6406645942136548967141809 4804984456602411725356357)
      ·
        refine ⟨900934585612952198504317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4804984456602411725356357 900934585612952198504317)
        ·
          refine ⟨337850469604857074439119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 900934585612952198504317 337850469604857074439119)
          ·
            refine ⟨506775704407285611658679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337850469604857074439119 506775704407285611658679)
            ·
              refine ⟨760163556610928417488019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506775704407285611658679 760163556610928417488019)
              ·
                refine ⟨1140245334916392626232029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760163556610928417488019 1140245334916392626232029)
                ·
                  refine ⟨427592000593647234837011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140245334916392626232029 427592000593647234837011)
                  ·
                    refine ⟨641388000890470852255517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427592000593647234837011 641388000890470852255517)
                    ·
                      refine ⟨240520500333926569595819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641388000890470852255517 240520500333926569595819)
                      ·
                        rfl

theorem cell23_468412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_468412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468412 prefixEnd_468412 := by exact prefixLift 468412
  have htrace : WordTrace (prefixWord ++ tailWord_468412) baseStart_468412 baseEnd_468412 := by
    simpa [prefixWord, tailWord_468412, baseEnd_468412] using wordTrace_append hprefix tailTrace_468412
  have hstable : (prefixWord ++ tailWord_468412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468412).length < 2 ^ (prefixWord ++ tailWord_468412).sum := by decide
  have hdescent : baseEnd_468412 < baseStart_468412 := by decide
  rcases family_descends (prefixWord ++ tailWord_468412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468424 : List Nat := [2, 1, 3, 1, 3, 1, 4, 8]
def baseStart_468424 : Nat := 118140960795 + 468424 * 2 ^ 59
def prefixEnd_468424 : Nat := 4983230072969 + 3 ^ 40 * 468424 * 2
def baseEnd_468424 : Nat := 8908394892658537875769

theorem tailTrace_468424 : CollatzResearch.WordTrace tailWord_468424 prefixEnd_468424 8908394892658537875769 := by
  unfold tailWord_468424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542413427493661647574163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11389884569991548863432217 8542413427493661647574163)
  ·
    refine ⟨12813620141240492471361245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8542413427493661647574163 12813620141240492471361245)
    ·
      refine ⟨4805107552965184676760467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12813620141240492471361245 4805107552965184676760467)
      ·
        refine ⟨7207661329447777015140701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805107552965184676760467 7207661329447777015140701)
        ·
          refine ⟨2702872998542916380677763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7207661329447777015140701 2702872998542916380677763)
          ·
            refine ⟨4054309497814374571016645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702872998542916380677763 4054309497814374571016645)
            ·
              refine ⟨760183030840195232065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4054309497814374571016645 760183030840195232065621)
              ·
                refine ⟨8908394892658537875769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 760183030840195232065621 8908394892658537875769)
                ·
                  rfl

theorem cell23_468424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 8].length) (baseStart_468424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468424 prefixEnd_468424 := by exact prefixLift 468424
  have htrace : WordTrace (prefixWord ++ tailWord_468424) baseStart_468424 baseEnd_468424 := by
    simpa [prefixWord, tailWord_468424, baseEnd_468424] using wordTrace_append hprefix tailTrace_468424
  have hstable : (prefixWord ++ tailWord_468424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468424).length < 2 ^ (prefixWord ++ tailWord_468424).sum := by decide
  have hdescent : baseEnd_468424 < baseStart_468424 := by decide
  rcases family_descends (prefixWord ++ tailWord_468424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468428 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_468428 : Nat := 118140960795 + 468428 * 2 ^ 59
def prefixEnd_468428 : Nat := 4983230072969 + 3 ^ 40 * 468428 * 2
def baseEnd_468428 : Nat := 80176238674799502331915

theorem tailTrace_468428 : CollatzResearch.WordTrace tailWord_468428 prefixEnd_468428 80176238674799502331915 := by
  unfold tailWord_468428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542486373486415989146969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11389981831315221318862625 8542486373486415989146969)
  ·
    refine ⟨6406864780114811991860227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8542486373486415989146969 6406864780114811991860227)
    ·
      refine ⟨9610297170172217987790341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406864780114811991860227 9610297170172217987790341)
      ·
        refine ⟨1801930719407290872710689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9610297170172217987790341 1801930719407290872710689)
        ·
          refine ⟨1351448039555468154533017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801930719407290872710689 1351448039555468154533017)
          ·
            refine ⟨1013586029666601115899763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351448039555468154533017 1013586029666601115899763)
            ·
              refine ⟨1520379044499901673849645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013586029666601115899763 1520379044499901673849645)
              ·
                refine ⟨570142141687463127693617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520379044499901673849645 570142141687463127693617)
                ·
                  refine ⟨427606606265597345770213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570142141687463127693617 427606606265597345770213)
                  ·
                    refine ⟨80176238674799502331915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427606606265597345770213 80176238674799502331915)
                    ·
                      rfl

theorem cell23_468428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_468428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468428 prefixEnd_468428 := by exact prefixLift 468428
  have htrace : WordTrace (prefixWord ++ tailWord_468428) baseStart_468428 baseEnd_468428 := by
    simpa [prefixWord, tailWord_468428, baseEnd_468428] using wordTrace_append hprefix tailTrace_468428
  have hstable : (prefixWord ++ tailWord_468428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468428).length < 2 ^ (prefixWord ++ tailWord_468428).sum := by decide
  have hdescent : baseEnd_468428 < baseStart_468428 := by decide
  rcases family_descends (prefixWord ++ tailWord_468428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468451 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3]
def baseStart_468451 : Nat := 118140960795 + 468451 * 2 ^ 59
def prefixEnd_468451 : Nat := 4983230072969 + 3 ^ 40 * 468451 * 2
def baseEnd_468451 : Nat := 240540526079451917008139

theorem tailTrace_468451 : CollatzResearch.WordTrace tailWord_468451 prefixEnd_468451 240540526079451917008139 := by
  unfold tailWord_468451
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085811625889506906381207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11390541083926337937587471 17085811625889506906381207)
  ·
    refine ⟨25628717438834260359571811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085811625889506906381207 25628717438834260359571811)
    ·
      refine ⟨38443076158251390539357717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25628717438834260359571811 38443076158251390539357717)
      ·
        refine ⟨1802019194918033931532393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38443076158251390539357717 1802019194918033931532393)
        ·
          refine ⟨1351514396188525448649295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802019194918033931532393 1351514396188525448649295)
          ·
            refine ⟨2027271594282788172973943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351514396188525448649295 2027271594282788172973943)
            ·
              refine ⟨3040907391424182259460915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027271594282788172973943 3040907391424182259460915)
              ·
                refine ⟨4561361087136273389191373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040907391424182259460915 4561361087136273389191373)
                ·
                  refine ⟨1710510407676102520946765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4561361087136273389191373 1710510407676102520946765)
                  ·
                    refine ⟨641441402878538445355037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1710510407676102520946765 641441402878538445355037)
                    ·
                      refine ⟨240540526079451917008139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641441402878538445355037 240540526079451917008139)
                      ·
                        rfl

theorem cell23_468451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_468451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468451 prefixEnd_468451 := by exact prefixLift 468451
  have htrace : WordTrace (prefixWord ++ tailWord_468451) baseStart_468451 baseEnd_468451 := by
    simpa [prefixWord, tailWord_468451, baseEnd_468451] using wordTrace_append hprefix tailTrace_468451
  have hstable : (prefixWord ++ tailWord_468451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468451).length < 2 ^ (prefixWord ++ tailWord_468451).sum := by decide
  have hdescent : baseEnd_468451 < baseStart_468451 := by decide
  rcases family_descends (prefixWord ++ tailWord_468451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468455 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_468455 : Nat := 118140960795 + 468455 * 2 ^ 59
def prefixEnd_468455 : Nat := 4983230072969 + 3 ^ 40 * 468455 * 2
def baseEnd_468455 : Nat := 240542580002069901358121

theorem tailTrace_468455 : CollatzResearch.WordTrace tailWord_468455 prefixEnd_468455 240542580002069901358121 := by
  unfold tailWord_468455
  simp only [CollatzResearch.WordTrace]
  refine ⟨17085957517875015589526819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11390638345250010393017879 17085957517875015589526819)
  ·
    refine ⟨25628936276812523384290229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17085957517875015589526819 25628936276812523384290229)
    ·
      refine ⟨2402712775951174067277209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25628936276812523384290229 2402712775951174067277209)
      ·
        refine ⟨1802034581963380550457907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402712775951174067277209 1802034581963380550457907)
        ·
          refine ⟨2703051872945070825686861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802034581963380550457907 2703051872945070825686861)
          ·
            refine ⟨1013644452354401559632573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2703051872945070825686861 1013644452354401559632573)
            ·
              refine ⟨380116669632900584862215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013644452354401559632573 380116669632900584862215)
              ·
                refine ⟨570175004449350877293323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380116669632900584862215 570175004449350877293323)
                ·
                  refine ⟨855262506674026315939985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570175004449350877293323 855262506674026315939985)
                  ·
                    refine ⟨641446880005519736954989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 855262506674026315939985 641446880005519736954989)
                    ·
                      refine ⟨240542580002069901358121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641446880005519736954989 240542580002069901358121)
                      ·
                        rfl

theorem cell23_468455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_468455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468455 prefixEnd_468455 := by exact prefixLift 468455
  have htrace : WordTrace (prefixWord ++ tailWord_468455) baseStart_468455 baseEnd_468455 := by
    simpa [prefixWord, tailWord_468455, baseEnd_468455] using wordTrace_append hprefix tailTrace_468455
  have hstable : (prefixWord ++ tailWord_468455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468455).length < 2 ^ (prefixWord ++ tailWord_468455).sum := by decide
  have hdescent : baseEnd_468455 < baseStart_468455 := by decide
  rcases family_descends (prefixWord ++ tailWord_468455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468469 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_468469 : Nat := 118140960795 + 468469 * 2 ^ 59
def prefixEnd_468469 : Nat := 4983230072969 + 3 ^ 40 * 468469 * 2
def baseEnd_468469 : Nat := 240549768731232846583057

theorem tailTrace_468469 : CollatzResearch.WordTrace tailWord_468469 prefixEnd_468469 240549768731232846583057 := by
  unfold tailWord_468469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086468139824295980536461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11390978759882863987024307 17086468139824295980536461)
  ·
    refine ⟨6407425552434110992701173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17086468139824295980536461 6407425552434110992701173)
    ·
      refine ⟨600696145540697905565735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6407425552434110992701173 600696145540697905565735)
      ·
        refine ⟨901044218311046858348603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600696145540697905565735 901044218311046858348603)
        ·
          refine ⟨1351566327466570287522905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901044218311046858348603 1351566327466570287522905)
          ·
            refine ⟨1013674745599927715642179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351566327466570287522905 1013674745599927715642179)
            ·
              refine ⟨1520512118399891573463269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013674745599927715642179 1520512118399891573463269)
              ·
                refine ⟨285096022199979670024363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1520512118399891573463269 285096022199979670024363)
                ·
                  refine ⟨427644033299969505036545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285096022199979670024363 427644033299969505036545)
                  ·
                    refine ⟨320733024974977128777409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427644033299969505036545 320733024974977128777409)
                    ·
                      refine ⟨240549768731232846583057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320733024974977128777409 240549768731232846583057)
                      ·
                        rfl

theorem cell23_468469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_468469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468469 prefixEnd_468469 := by exact prefixLift 468469
  have htrace : WordTrace (prefixWord ++ tailWord_468469) baseStart_468469 baseEnd_468469 := by
    simpa [prefixWord, tailWord_468469, baseEnd_468469] using wordTrace_append hprefix tailTrace_468469
  have hstable : (prefixWord ++ tailWord_468469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468469).length < 2 ^ (prefixWord ++ tailWord_468469).sum := by decide
  have hdescent : baseEnd_468469 < baseStart_468469 := by decide
  rcases family_descends (prefixWord ++ tailWord_468469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468474 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_468474 : Nat := 118140960795 + 468474 * 2 ^ 59
def prefixEnd_468474 : Nat := 4983230072969 + 3 ^ 40 * 468474 * 2
def baseEnd_468474 : Nat := 240552336134505327020533

theorem tailTrace_468474 : CollatzResearch.WordTrace tailWord_468474 prefixEnd_468474 240552336134505327020533 := by
  unfold tailWord_468474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271662626201545458617119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11391100336537454556312317 4271662626201545458617119)
  ·
    refine ⟨6407493939302318187925679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271662626201545458617119 6407493939302318187925679)
    ·
      refine ⟨9611240908953477281888519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6407493939302318187925679 9611240908953477281888519)
      ·
        refine ⟨14416861363430215922832779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611240908953477281888519 14416861363430215922832779)
        ·
          refine ⟨21625292045145323884249169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416861363430215922832779 21625292045145323884249169)
          ·
            refine ⟨16218969033858992913186877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21625292045145323884249169 16218969033858992913186877)
            ·
              refine ⟨6082113387697122342445079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16218969033858992913186877 6082113387697122342445079)
              ·
                refine ⟨9123170081545683513667619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082113387697122342445079 9123170081545683513667619)
                ·
                  refine ⟨13684755122318525270501429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123170081545683513667619 13684755122318525270501429)
                  ·
                    refine ⟨1282945792717361744109509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13684755122318525270501429 1282945792717361744109509)
                    ·
                      refine ⟨240552336134505327020533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1282945792717361744109509 240552336134505327020533)
                      ·
                        rfl

theorem cell23_468474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_468474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468474 prefixEnd_468474 := by exact prefixLift 468474
  have htrace : WordTrace (prefixWord ++ tailWord_468474) baseStart_468474 baseEnd_468474 := by
    simpa [prefixWord, tailWord_468474, baseEnd_468474] using wordTrace_append hprefix tailTrace_468474
  have hstable : (prefixWord ++ tailWord_468474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468474).length < 2 ^ (prefixWord ++ tailWord_468474).sum := by decide
  have hdescent : baseEnd_468474 < baseStart_468474 := by decide
  rcases family_descends (prefixWord ++ tailWord_468474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468486 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_468486 : Nat := 118140960795 + 468486 * 2 ^ 59
def prefixEnd_468486 : Nat := 4983230072969 + 3 ^ 40 * 468486 * 2
def baseEnd_468486 : Nat := 240558497902359280070479

theorem tailTrace_468486 : CollatzResearch.WordTrace tailWord_468486 prefixEnd_468486 240558497902359280070479 := by
  unfold tailWord_468486
  simp only [CollatzResearch.WordTrace]
  refine ⟨533971505648834621372041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11391392120508471922603541 533971505648834621372041)
  ·
    refine ⟨400478629236625966029031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 533971505648834621372041 400478629236625966029031)
    ·
      refine ⟨600717943854938949043547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400478629236625966029031 600717943854938949043547)
      ·
        refine ⟨901076915782408423565321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600717943854938949043547 901076915782408423565321)
        ·
          refine ⟨675807686836806317673991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901076915782408423565321 675807686836806317673991)
          ·
            refine ⟨1013711530255209476510987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675807686836806317673991 1013711530255209476510987)
            ·
              refine ⟨1520567295382814214766481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013711530255209476510987 1520567295382814214766481)
              ·
                refine ⟨1140425471537110661074861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520567295382814214766481 1140425471537110661074861)
                ·
                  refine ⟨427659551826416497903073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140425471537110661074861 427659551826416497903073)
                  ·
                    refine ⟨320744663869812373427305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427659551826416497903073 320744663869812373427305)
                    ·
                      refine ⟨240558497902359280070479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320744663869812373427305 240558497902359280070479)
                      ·
                        rfl

theorem cell23_468486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_468486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468486 prefixEnd_468486 := by exact prefixLift 468486
  have htrace : WordTrace (prefixWord ++ tailWord_468486) baseStart_468486 baseEnd_468486 := by
    simpa [prefixWord, tailWord_468486, baseEnd_468486] using wordTrace_append hprefix tailTrace_468486
  have hstable : (prefixWord ++ tailWord_468486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468486).length < 2 ^ (prefixWord ++ tailWord_468486).sum := by decide
  have hdescent : baseEnd_468486 < baseStart_468486 := by decide
  rcases family_descends (prefixWord ++ tailWord_468486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468508 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_468508 : Nat := 118140960795 + 468508 * 2 ^ 59
def prefixEnd_468508 : Nat := 4983230072969 + 3 ^ 40 * 468508 * 2
def baseEnd_468508 : Nat := 240569794476758193995377

theorem tailTrace_468508 : CollatzResearch.WordTrace tailWord_468508 prefixEnd_468508 240569794476758193995377 := by
  unfold tailWord_468508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543945293341502820603089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11391927057788670427470785 8543945293341502820603089)
  ·
    refine ⟨6407958970006127115452317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8543945293341502820603089 6407958970006127115452317)
    ·
      refine ⟨2402984613752297668294619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6407958970006127115452317 2402984613752297668294619)
      ·
        refine ⟨3604476920628446502441929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402984613752297668294619 3604476920628446502441929)
        ·
          refine ⟨2703357690471334876831447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604476920628446502441929 2703357690471334876831447)
          ·
            refine ⟨4055036535707002315247171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703357690471334876831447 4055036535707002315247171)
            ·
              refine ⟨6082554803560503472870757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055036535707002315247171 6082554803560503472870757)
              ·
                refine ⟨1140479025667594401163267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6082554803560503472870757 1140479025667594401163267)
                ·
                  refine ⟨1710718538501391601744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140479025667594401163267 1710718538501391601744901)
                  ·
                    refine ⟨320759725969010925327169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1710718538501391601744901 320759725969010925327169)
                    ·
                      refine ⟨240569794476758193995377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320759725969010925327169 240569794476758193995377)
                      ·
                        rfl

theorem cell23_468508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_468508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468508 prefixEnd_468508 := by exact prefixLift 468508
  have htrace : WordTrace (prefixWord ++ tailWord_468508) baseStart_468508 baseEnd_468508 := by
    simpa [prefixWord, tailWord_468508, baseEnd_468508] using wordTrace_append hprefix tailTrace_468508
  have hstable : (prefixWord ++ tailWord_468508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468508).length < 2 ^ (prefixWord ++ tailWord_468508).sum := by decide
  have hdescent : baseEnd_468508 < baseStart_468508 := by decide
  rcases family_descends (prefixWord ++ tailWord_468508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468512 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2]
def baseStart_468512 : Nat := 118140960795 + 468512 * 2 ^ 59
def prefixEnd_468512 : Nat := 4983230072969 + 3 ^ 40 * 468512 * 2
def baseEnd_468512 : Nat := 240571848399376178345359

theorem tailTrace_468512 : CollatzResearch.WordTrace tailWord_468512 prefixEnd_468512 240571848399376178345359 := by
  unfold tailWord_468512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544018239334257162175895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11392024319112342882901193 8544018239334257162175895)
  ·
    refine ⟨12816027359001385743263843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544018239334257162175895 12816027359001385743263843)
    ·
      refine ⟨19224041038502078614895765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816027359001385743263843 19224041038502078614895765)
      ·
        refine ⟨901126923679784935073239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19224041038502078614895765 901126923679784935073239)
        ·
          refine ⟨1351690385519677402609859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901126923679784935073239 1351690385519677402609859)
          ·
            refine ⟨2027535578279516103914789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351690385519677402609859 2027535578279516103914789)
            ·
              refine ⟨380162920927409269484023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2027535578279516103914789 380162920927409269484023)
              ·
                refine ⟨570244381391113904226035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380162920927409269484023 570244381391113904226035)
                ·
                  refine ⟨855366572086670856339053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570244381391113904226035 855366572086670856339053)
                  ·
                    refine ⟨320762464532501571127145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 855366572086670856339053 320762464532501571127145)
                    ·
                      refine ⟨240571848399376178345359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320762464532501571127145 240571848399376178345359)
                      ·
                        rfl

theorem cell23_468512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_468512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468512 prefixEnd_468512 := by exact prefixLift 468512
  have htrace : WordTrace (prefixWord ++ tailWord_468512) baseStart_468512 baseEnd_468512 := by
    simpa [prefixWord, tailWord_468512, baseEnd_468512] using wordTrace_append hprefix tailTrace_468512
  have hstable : (prefixWord ++ tailWord_468512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468512).length < 2 ^ (prefixWord ++ tailWord_468512).sum := by decide
  have hdescent : baseEnd_468512 < baseStart_468512 := by decide
  rcases family_descends (prefixWord ++ tailWord_468512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468531 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 7]
def baseStart_468531 : Nat := 118140960795 + 468531 * 2 ^ 59
def prefixEnd_468531 : Nat := 4983230072969 + 3 ^ 40 * 468531 * 2
def baseEnd_468531 : Nat := 26731289392423511556419

theorem tailTrace_468531 : CollatzResearch.WordTrace tailWord_468531 prefixEnd_468531 26731289392423511556419 := by
  unfold tailWord_468531
  simp only [CollatzResearch.WordTrace]
  refine ⟨17088729465599680569293447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11392486310399787046195631 17088729465599680569293447)
  ·
    refine ⟨25633094198399520853940171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17088729465599680569293447 25633094198399520853940171)
    ·
      refine ⟨38449641297599281280910257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25633094198399520853940171 38449641297599281280910257)
      ·
        refine ⟨28837230973199460960682693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38449641297599281280910257 28837230973199460960682693)
        ·
          refine ⟨5406980807474898930128005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28837230973199460960682693 5406980807474898930128005)
          ·
            refine ⟨1013808901401543549399001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5406980807474898930128005 1013808901401543549399001)
            ·
              refine ⟨760356676051157662049251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013808901401543549399001 760356676051157662049251)
              ·
                refine ⟨1140535014076736493073877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760356676051157662049251 1140535014076736493073877)
                ·
                  refine ⟨26731289392423511556419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1140535014076736493073877 26731289392423511556419)
                  ·
                    rfl

theorem cell23_468531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 7].length) (baseStart_468531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468531 prefixEnd_468531 := by exact prefixLift 468531
  have htrace : WordTrace (prefixWord ++ tailWord_468531) baseStart_468531 baseEnd_468531 := by
    simpa [prefixWord, tailWord_468531, baseEnd_468531] using wordTrace_append hprefix tailTrace_468531
  have hstable : (prefixWord ++ tailWord_468531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468531).length < 2 ^ (prefixWord ++ tailWord_468531).sum := by decide
  have hdescent : baseEnd_468531 < baseStart_468531 := by decide
  rcases family_descends (prefixWord ++ tailWord_468531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468561 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_468561 : Nat := 118140960795 + 468561 * 2 ^ 59
def prefixEnd_468561 : Nat := 4983230072969 + 3 ^ 40 * 468561 * 2
def baseEnd_468561 : Nat := 80199002983815495544211

theorem tailTrace_468561 : CollatzResearch.WordTrace tailWord_468561 prefixEnd_468561 80199002983815495544211 := by
  unfold tailWord_468561
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089823655490995692885537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11393215770327330461923691 17089823655490995692885537)
  ·
    refine ⟨12817367741618246769664153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17089823655490995692885537 12817367741618246769664153)
    ·
      refine ⟨9613025806213685077248115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817367741618246769664153 9613025806213685077248115)
      ·
        refine ⟨14419538709320527615872173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613025806213685077248115 14419538709320527615872173)
        ·
          refine ⟨5407327015995197855952065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14419538709320527615872173 5407327015995197855952065)
          ·
            refine ⟨4055495261996398391964049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407327015995197855952065 4055495261996398391964049)
            ·
              refine ⟨3041621446497298793973037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055495261996398391964049 3041621446497298793973037)
              ·
                refine ⟨1140608042436487047739889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3041621446497298793973037 1140608042436487047739889)
                ·
                  refine ⟨855456031827365285804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1140608042436487047739889 855456031827365285804917)
                  ·
                    refine ⟨80199002983815495544211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 855456031827365285804917 80199002983815495544211)
                    ·
                      rfl

theorem cell23_468561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_468561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468561 prefixEnd_468561 := by exact prefixLift 468561
  have htrace : WordTrace (prefixWord ++ tailWord_468561) baseStart_468561 baseEnd_468561 := by
    simpa [prefixWord, tailWord_468561, baseEnd_468561] using wordTrace_append hprefix tailTrace_468561
  have hstable : (prefixWord ++ tailWord_468561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468561).length < 2 ^ (prefixWord ++ tailWord_468561).sum := by decide
  have hdescent : baseEnd_468561 < baseStart_468561 := by decide
  rcases family_descends (prefixWord ++ tailWord_468561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468668 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_468668 : Nat := 118140960795 + 468668 * 2 ^ 59
def prefixEnd_468668 : Nat := 4983230072969 + 3 ^ 40 * 468668 * 2
def baseEnd_468668 : Nat := 80217317127159189331547

theorem tailTrace_468668 : CollatzResearch.WordTrace tailWord_468668 prefixEnd_468668 80217317127159189331547 := by
  unfold tailWord_468668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546863133051676483515329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11395817510735568644687105 8546863133051676483515329)
  ·
    refine ⟨6410147349788757362636497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8546863133051676483515329 6410147349788757362636497)
    ·
      refine ⟨4807610512341568021977373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6410147349788757362636497 4807610512341568021977373)
      ·
        refine ⟨1802853942128088008241515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4807610512341568021977373 1802853942128088008241515)
        ·
          refine ⟨2704280913192132012362273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802853942128088008241515 2704280913192132012362273)
          ·
            refine ⟨2028210684894099009271705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704280913192132012362273 2028210684894099009271705)
            ·
              refine ⟨1521158013670574256953779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028210684894099009271705 1521158013670574256953779)
              ·
                refine ⟨2281737020505861385430669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521158013670574256953779 2281737020505861385430669)
                ·
                  refine ⟨855651382689698019536501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2281737020505861385430669 855651382689698019536501)
                  ·
                    refine ⟨80217317127159189331547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 855651382689698019536501 80217317127159189331547)
                    ·
                      rfl

theorem cell23_468668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_468668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468668 prefixEnd_468668 := by exact prefixLift 468668
  have htrace : WordTrace (prefixWord ++ tailWord_468668) baseStart_468668 baseEnd_468668 := by
    simpa [prefixWord, tailWord_468668, baseEnd_468668] using wordTrace_append hprefix tailTrace_468668
  have hstable : (prefixWord ++ tailWord_468668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468668).length < 2 ^ (prefixWord ++ tailWord_468668).sum := by decide
  have hdescent : baseEnd_468668 < baseStart_468668 := by decide
  rcases family_descends (prefixWord ++ tailWord_468668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468708 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_468708 : Nat := 118140960795 + 468708 * 2 ^ 59
def prefixEnd_468708 : Nat := 4983230072969 + 3 ^ 40 * 468708 * 2
def baseEnd_468708 : Nat := 240672490607657411494457

theorem tailTrace_468708 : CollatzResearch.WordTrace tailWord_468708 prefixEnd_468708 240672490607657411494457 := by
  unfold tailWord_468708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547592592979219899243389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11396790123972293198991185 8547592592979219899243389)
  ·
    refine ⟨3205347222367207462216271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8547592592979219899243389 3205347222367207462216271)
    ·
      refine ⟨4808020833550811193324407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205347222367207462216271 4808020833550811193324407)
      ·
        refine ⟨7212031250326216789986611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808020833550811193324407 7212031250326216789986611)
        ·
          refine ⟨10818046875489325184979917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212031250326216789986611 10818046875489325184979917)
          ·
            refine ⟨4056767578308496944367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10818046875489325184979917 4056767578308496944367469)
            ·
              refine ⟨1521287841865686354137801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056767578308496944367469 1521287841865686354137801)
              ·
                refine ⟨1140965881399264765603351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521287841865686354137801 1140965881399264765603351)
                ·
                  refine ⟨1711448822098897148405027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1140965881399264765603351 1711448822098897148405027)
                  ·
                    refine ⟨2567173233148345722607541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1711448822098897148405027 2567173233148345722607541)
                    ·
                      refine ⟨240672490607657411494457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2567173233148345722607541 240672490607657411494457)
                      ·
                        rfl

theorem cell23_468708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_468708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468708 prefixEnd_468708 := by exact prefixLift 468708
  have htrace : WordTrace (prefixWord ++ tailWord_468708) baseStart_468708 baseEnd_468708 := by
    simpa [prefixWord, tailWord_468708, baseEnd_468708] using wordTrace_append hprefix tailTrace_468708
  have hstable : (prefixWord ++ tailWord_468708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468708).length < 2 ^ (prefixWord ++ tailWord_468708).sum := by decide
  have hdescent : baseEnd_468708 < baseStart_468708 := by decide
  rcases family_descends (prefixWord ++ tailWord_468708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468718 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_468718 : Nat := 118140960795 + 468718 * 2 ^ 59
def prefixEnd_468718 : Nat := 4983230072969 + 3 ^ 40 * 468718 * 2
def baseEnd_468718 : Nat := 240677625414202372369411

theorem tailTrace_468718 : CollatzResearch.WordTrace tailWord_468718 prefixEnd_468718 240677625414202372369411 := by
  unfold tailWord_468718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136943739490276438293851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11397033277281474337567205 2136943739490276438293851)
  ·
    refine ⟨3205415609235414657440777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2136943739490276438293851 3205415609235414657440777)
    ·
      refine ⟨2404061706926560993080583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205415609235414657440777 2404061706926560993080583)
      ·
        refine ⟨3606092560389841489620875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404061706926560993080583 3606092560389841489620875)
        ·
          refine ⟨5409138840584762234431313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606092560389841489620875 5409138840584762234431313)
          ·
            refine ⟨4056854130438571675823485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409138840584762234431313 4056854130438571675823485)
            ·
              refine ⟨1521320298914464378433807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4056854130438571675823485 1521320298914464378433807)
              ·
                refine ⟨2281980448371696567650711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521320298914464378433807 2281980448371696567650711)
                ·
                  refine ⟨3422970672557544851476067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281980448371696567650711 3422970672557544851476067)
                  ·
                    refine ⟨5134456008836317277214101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422970672557544851476067 5134456008836317277214101)
                    ·
                      refine ⟨240677625414202372369411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5134456008836317277214101 240677625414202372369411)
                      ·
                        rfl

theorem cell23_468718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_468718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468718 prefixEnd_468718 := by exact prefixLift 468718
  have htrace : WordTrace (prefixWord ++ tailWord_468718) baseStart_468718 baseEnd_468718 := by
    simpa [prefixWord, tailWord_468718, baseEnd_468718] using wordTrace_append hprefix tailTrace_468718
  have hstable : (prefixWord ++ tailWord_468718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468718).length < 2 ^ (prefixWord ++ tailWord_468718).sum := by decide
  have hdescent : baseEnd_468718 < baseStart_468718 := by decide
  rcases family_descends (prefixWord ++ tailWord_468718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468722 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_468722 : Nat := 118140960795 + 468722 * 2 ^ 59
def prefixEnd_468722 : Nat := 4983230072969 + 3 ^ 40 * 468722 * 2
def baseEnd_468722 : Nat := 240679679336820356719393

theorem tailTrace_468722 : CollatzResearch.WordTrace tailWord_468722 prefixEnd_468722 240679679336820356719393 := by
  unfold tailWord_468722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273923951976930047374105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11397130538605146792997613 4273923951976930047374105)
  ·
    refine ⟨3205442963982697535530579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4273923951976930047374105 3205442963982697535530579)
    ·
      refine ⟨4808164445974046303295869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205442963982697535530579 4808164445974046303295869)
      ·
        refine ⟨1803061667240267363735951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4808164445974046303295869 1803061667240267363735951)
        ·
          refine ⟨2704592500860401045603927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803061667240267363735951 2704592500860401045603927)
          ·
            refine ⟨4056888751290601568405891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704592500860401045603927 4056888751290601568405891)
            ·
              refine ⟨6085333126935902352608837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056888751290601568405891 6085333126935902352608837)
              ·
                refine ⟨1140999961300481691114157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6085333126935902352608837 1140999961300481691114157)
                ·
                  refine ⟨427874985487680634167809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140999961300481691114157 427874985487680634167809)
                  ·
                    refine ⟨320906239115760475625857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427874985487680634167809 320906239115760475625857)
                    ·
                      refine ⟨240679679336820356719393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320906239115760475625857 240679679336820356719393)
                      ·
                        rfl

theorem cell23_468722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_468722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468722 prefixEnd_468722 := by exact prefixLift 468722
  have htrace : WordTrace (prefixWord ++ tailWord_468722) baseStart_468722 baseEnd_468722 := by
    simpa [prefixWord, tailWord_468722, baseEnd_468722] using wordTrace_append hprefix tailTrace_468722
  have hstable : (prefixWord ++ tailWord_468722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468722).length < 2 ^ (prefixWord ++ tailWord_468722).sum := by decide
  have hdescent : baseEnd_468722 < baseStart_468722 := by decide
  rcases family_descends (prefixWord ++ tailWord_468722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468739 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 1, 2, 2]
def baseStart_468739 : Nat := 118140960795 + 468739 * 2 ^ 59
def prefixEnd_468739 : Nat := 4983230072969 + 3 ^ 40 * 468739 * 2
def baseEnd_468739 : Nat := 240688408507946790206815

theorem tailTrace_468739 : CollatzResearch.WordTrace tailWord_468739 prefixEnd_468739 240688408507946790206815 := by
  unfold tailWord_468739
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096315848846132092865271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11397543899230754728576847 17096315848846132092865271)
  ·
    refine ⟨25644473773269198139297907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17096315848846132092865271 25644473773269198139297907)
    ·
      refine ⟨38466710659903797208946861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25644473773269198139297907 38466710659903797208946861)
      ·
        refine ⟨14425016497463923953355073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38466710659903797208946861 14425016497463923953355073)
        ·
          refine ⟨10818762373097942965016305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14425016497463923953355073 10818762373097942965016305)
          ·
            refine ⟨8114071779823457223762229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10818762373097942965016305 8114071779823457223762229)
            ·
              refine ⟨760694229358449114727709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8114071779823457223762229 760694229358449114727709)
              ·
                refine ⟨285260336009418418022891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760694229358449114727709 285260336009418418022891)
                ·
                  refine ⟨427890504014127627034337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285260336009418418022891 427890504014127627034337)
                  ·
                    refine ⟨320917878010595720275753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 427890504014127627034337 320917878010595720275753)
                    ·
                      refine ⟨240688408507946790206815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 320917878010595720275753 240688408507946790206815)
                      ·
                        rfl

theorem cell23_468739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_468739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468739 prefixEnd_468739 := by exact prefixLift 468739
  have htrace : WordTrace (prefixWord ++ tailWord_468739) baseStart_468739 baseEnd_468739 := by
    simpa [prefixWord, tailWord_468739, baseEnd_468739] using wordTrace_append hprefix tailTrace_468739
  have hstable : (prefixWord ++ tailWord_468739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468739).length < 2 ^ (prefixWord ++ tailWord_468739).sum := by decide
  have hdescent : baseEnd_468739 < baseStart_468739 := by decide
  rcases family_descends (prefixWord ++ tailWord_468739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468741 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_468741 : Nat := 118140960795 + 468741 * 2 ^ 59
def prefixEnd_468741 : Nat := 4983230072969 + 3 ^ 40 * 468741 * 2
def baseEnd_468741 : Nat := 80229811823085260793935

theorem tailTrace_468741 : CollatzResearch.WordTrace tailWord_468741 prefixEnd_468741 80229811823085260793935 := by
  unfold tailWord_468741
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096388794838886434438077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11397592529892590956292051 17096388794838886434438077)
  ·
    refine ⟨6411145798064582412914279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17096388794838886434438077 6411145798064582412914279)
    ·
      refine ⟨9616718697096873619371419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411145798064582412914279 9616718697096873619371419)
      ·
        refine ⟨14425078045645310429057129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616718697096873619371419 14425078045645310429057129)
        ·
          refine ⟨10818808534233982821792847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14425078045645310429057129 10818808534233982821792847)
          ·
            refine ⟨16228212801350974232689271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10818808534233982821792847 16228212801350974232689271)
            ·
              refine ⟨24342319202026461349033907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228212801350974232689271 24342319202026461349033907)
              ·
                refine ⟨36513478803039692023550861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24342319202026461349033907 36513478803039692023550861)
                ·
                  refine ⟨13692554551139884508831573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36513478803039692023550861 13692554551139884508831573)
                  ·
                    refine ⟨80229811823085260793935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13692554551139884508831573 80229811823085260793935)
                    ·
                      rfl

theorem cell23_468741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_468741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468741 prefixEnd_468741 := by exact prefixLift 468741
  have htrace : WordTrace (prefixWord ++ tailWord_468741) baseStart_468741 baseEnd_468741 := by
    simpa [prefixWord, tailWord_468741, baseEnd_468741] using wordTrace_append hprefix tailTrace_468741
  have hstable : (prefixWord ++ tailWord_468741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468741).length < 2 ^ (prefixWord ++ tailWord_468741).sum := by decide
  have hdescent : baseEnd_468741 < baseStart_468741 := by decide
  rcases family_descends (prefixWord ++ tailWord_468741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468761 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_468761 : Nat := 118140960795 + 468761 * 2 ^ 59
def prefixEnd_468761 : Nat := 4983230072969 + 3 ^ 40 * 468761 * 2
def baseEnd_468761 : Nat := 240699705082345704131713

theorem tailTrace_468761 : CollatzResearch.WordTrace tailWord_468761 prefixEnd_468761 240699705082345704131713 := by
  unfold tailWord_468761
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097118254766429850166137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11398078836510953233444091 17097118254766429850166137)
  ·
    refine ⟨12822838691074822387624603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17097118254766429850166137 12822838691074822387624603)
    ·
      refine ⟨19234258036612233581436905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12822838691074822387624603 19234258036612233581436905)
      ·
        refine ⟨14425693527459175186077679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19234258036612233581436905 14425693527459175186077679)
        ·
          refine ⟨21638540291188762779116519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425693527459175186077679 21638540291188762779116519)
          ·
            refine ⟨32457810436783144168674779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21638540291188762779116519 32457810436783144168674779)
            ·
              refine ⟨48686715655174716253012169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32457810436783144168674779 48686715655174716253012169)
              ·
                refine ⟨36515036741381037189759127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48686715655174716253012169 36515036741381037189759127)
                ·
                  refine ⟨54772555112071555784638691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36515036741381037189759127 54772555112071555784638691)
                  ·
                    refine ⟨82158832668107333676958037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54772555112071555784638691 82158832668107333676958037)
                    ·
                      refine ⟨240699705082345704131713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 82158832668107333676958037 240699705082345704131713)
                      ·
                        rfl

theorem cell23_468761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_468761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468761 prefixEnd_468761 := by exact prefixLift 468761
  have htrace : WordTrace (prefixWord ++ tailWord_468761) baseStart_468761 baseEnd_468761 := by
    simpa [prefixWord, tailWord_468761, baseEnd_468761] using wordTrace_append hprefix tailTrace_468761
  have hstable : (prefixWord ++ tailWord_468761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468761).length < 2 ^ (prefixWord ++ tailWord_468761).sum := by decide
  have hdescent : baseEnd_468761 < baseStart_468761 := by decide
  rcases family_descends (prefixWord ++ tailWord_468761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468766 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_468766 : Nat := 118140960795 + 468766 * 2 ^ 59
def prefixEnd_468766 : Nat := 4983230072969 + 3 ^ 40 * 468766 * 2
def baseEnd_468766 : Nat := 80234090828539394856397

theorem tailTrace_468766 : CollatzResearch.WordTrace tailWord_468766 prefixEnd_468766 80234090828539394856397 := by
  unfold tailWord_468766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137162577468539463012269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11398200413165543802732101 2137162577468539463012269)
  ·
    refine ⟨801435966550702298629601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2137162577468539463012269 801435966550702298629601)
    ·
      refine ⟨601076974913026723972201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 801435966550702298629601 601076974913026723972201)
      ·
        refine ⟨450807731184770042979151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601076974913026723972201 450807731184770042979151)
        ·
          refine ⟨676211596777155064468727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450807731184770042979151 676211596777155064468727)
          ·
            refine ⟨1014317395165732596703091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676211596777155064468727 1014317395165732596703091)
            ·
              refine ⟨1521476092748598895054637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014317395165732596703091 1521476092748598895054637)
              ·
                refine ⟨570553534780724585645489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521476092748598895054637 570553534780724585645489)
                ·
                  refine ⟨427915151085543439234117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570553534780724585645489 427915151085543439234117)
                  ·
                    refine ⟨80234090828539394856397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427915151085543439234117 80234090828539394856397)
                    ·
                      rfl

theorem cell23_468766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_468766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468766 prefixEnd_468766 := by exact prefixLift 468766
  have htrace : WordTrace (prefixWord ++ tailWord_468766) baseStart_468766 baseEnd_468766 := by
    simpa [prefixWord, tailWord_468766, baseEnd_468766] using wordTrace_append hprefix tailTrace_468766
  have hstable : (prefixWord ++ tailWord_468766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468766).length < 2 ^ (prefixWord ++ tailWord_468766).sum := by decide
  have hdescent : baseEnd_468766 < baseStart_468766 := by decide
  rcases family_descends (prefixWord ++ tailWord_468766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468806 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_468806 : Nat := 118140960795 + 468806 * 2 ^ 59
def prefixEnd_468806 : Nat := 4983230072969 + 3 ^ 40 * 468806 * 2
def baseEnd_468806 : Nat := 240722811711798028069007

theorem tailTrace_468806 : CollatzResearch.WordTrace tailWord_468806 prefixEnd_468806 240722811711798028069007 := by
  unfold tailWord_468806
  simp only [CollatzResearch.WordTrace]
  refine ⟨534336235612606329236071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11399173026402268357036181 534336235612606329236071)
  ·
    refine ⟨801504353418909493854107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534336235612606329236071 801504353418909493854107)
    ·
      refine ⟨1202256530128364240781161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801504353418909493854107 1202256530128364240781161)
      ·
        refine ⟨901692397596273180585871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1202256530128364240781161 901692397596273180585871)
        ·
          refine ⟨1352538596394409770878807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901692397596273180585871 1352538596394409770878807)
          ·
            refine ⟨2028807894591614656318211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352538596394409770878807 2028807894591614656318211)
            ·
              refine ⟨3043211841887421984477317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028807894591614656318211 3043211841887421984477317)
              ·
                refine ⟨570602220353891622089497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3043211841887421984477317 570602220353891622089497)
                ·
                  refine ⟨427951665265418716567123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570602220353891622089497 427951665265418716567123)
                  ·
                    refine ⟨641927497898128074850685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 427951665265418716567123 641927497898128074850685)
                    ·
                      refine ⟨240722811711798028069007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 641927497898128074850685 240722811711798028069007)
                      ·
                        rfl

theorem cell23_468806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_468806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468806 prefixEnd_468806 := by exact prefixLift 468806
  have htrace : WordTrace (prefixWord ++ tailWord_468806) baseStart_468806 baseEnd_468806 := by
    simpa [prefixWord, tailWord_468806, baseEnd_468806] using wordTrace_append hprefix tailTrace_468806
  have hstable : (prefixWord ++ tailWord_468806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468806).length < 2 ^ (prefixWord ++ tailWord_468806).sum := by decide
  have hdescent : baseEnd_468806 < baseStart_468806 := by decide
  rcases family_descends (prefixWord ++ tailWord_468806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468835 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 7]
def baseStart_468835 : Nat := 118140960795 + 468835 * 2 ^ 59
def prefixEnd_468835 : Nat := 4983230072969 + 3 ^ 40 * 468835 * 2
def baseEnd_468835 : Nat := 26748633627864268289597

theorem tailTrace_468835 : CollatzResearch.WordTrace tailWord_468835 prefixEnd_468835 26748633627864268289597 := by
  unfold tailWord_468835
  simp only [CollatzResearch.WordTrace]
  refine ⟨17099817256498340488359959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11399878170998893658906639 17099817256498340488359959)
  ·
    refine ⟨25649725884747510732539939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17099817256498340488359959 25649725884747510732539939)
    ·
      refine ⟨38474588827121266098809909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25649725884747510732539939 38474588827121266098809909)
      ·
        refine ⟨3606992702542618696763429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38474588827121266098809909 3606992702542618696763429)
        ·
          refine ⟨676311131726741005643143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3606992702542618696763429 676311131726741005643143)
          ·
            refine ⟨1014466697590111508464715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676311131726741005643143 1014466697590111508464715)
            ·
              refine ⟨1521700046385167262697073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014466697590111508464715 1521700046385167262697073)
              ·
                refine ⟨1141275034788875447022805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521700046385167262697073 1141275034788875447022805)
                ·
                  refine ⟨26748633627864268289597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1141275034788875447022805 26748633627864268289597)
                  ·
                    rfl

theorem cell23_468835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 7].length) (baseStart_468835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468835 prefixEnd_468835 := by exact prefixLift 468835
  have htrace : WordTrace (prefixWord ++ tailWord_468835) baseStart_468835 baseEnd_468835 := by
    simpa [prefixWord, tailWord_468835, baseEnd_468835] using wordTrace_append hprefix tailTrace_468835
  have hstable : (prefixWord ++ tailWord_468835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468835).length < 2 ^ (prefixWord ++ tailWord_468835).sum := by decide
  have hdescent : baseEnd_468835 < baseStart_468835 := by decide
  rcases family_descends (prefixWord ++ tailWord_468835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468858 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_468858 : Nat := 118140960795 + 468858 * 2 ^ 59
def prefixEnd_468858 : Nat := 4983230072969 + 3 ^ 40 * 468858 * 2
def baseEnd_468858 : Nat := 240749512705831824618767

theorem tailTrace_468858 : CollatzResearch.WordTrace tailWord_468858 prefixEnd_468858 240749512705831824618767 := by
  unfold tailWord_468858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275164033853753854111807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11400437423610010277631485 4275164033853753854111807)
  ·
    refine ⟨6412746050780630781167711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275164033853753854111807 6412746050780630781167711)
    ·
      refine ⟨9619119076170946171751567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412746050780630781167711 9619119076170946171751567)
      ·
        refine ⟨14428678614256419257627351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619119076170946171751567 14428678614256419257627351)
        ·
          refine ⟨21643017921384628886441027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428678614256419257627351 21643017921384628886441027)
          ·
            refine ⟨32464526882076943329661541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21643017921384628886441027 32464526882076943329661541)
            ·
              refine ⟨6087098790389426874311539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32464526882076943329661541 6087098790389426874311539)
              ·
                refine ⟨9130648185584140311467309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087098790389426874311539 9130648185584140311467309)
                ·
                  refine ⟨3423993069594052616800241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9130648185584140311467309 3423993069594052616800241)
                  ·
                    refine ⟨2567994802195539462600181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423993069594052616800241 2567994802195539462600181)
                    ·
                      refine ⟨240749512705831824618767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2567994802195539462600181 240749512705831824618767)
                      ·
                        rfl

theorem cell23_468858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_468858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468858 prefixEnd_468858 := by exact prefixLift 468858
  have htrace : WordTrace (prefixWord ++ tailWord_468858) baseStart_468858 baseEnd_468858 := by
    simpa [prefixWord, tailWord_468858, baseEnd_468858] using wordTrace_append hprefix tailTrace_468858
  have hstable : (prefixWord ++ tailWord_468858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468858).length < 2 ^ (prefixWord ++ tailWord_468858).sum := by decide
  have hdescent : baseEnd_468858 < baseStart_468858 := by decide
  rcases family_descends (prefixWord ++ tailWord_468858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468925 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 8]
def baseStart_468925 : Nat := 118140960795 + 468925 * 2 ^ 59
def prefixEnd_468925 : Nat := 4983230072969 + 3 ^ 40 * 468925 * 2
def baseEnd_468925 : Nat := 26753768434409229164551

theorem tailTrace_468925 : CollatzResearch.WordTrace tailWord_468925 prefixEnd_468925 26753768434409229164551 := by
  unfold tailWord_468925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103099826172285859136229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11402066550781523906090819 17103099826172285859136229)
  ·
    refine ⟨3206831217407303598588043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17103099826172285859136229 3206831217407303598588043)
    ·
      refine ⟨4810246826110955397882065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206831217407303598588043 4810246826110955397882065)
      ·
        refine ⟨3607685119583216548411549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4810246826110955397882065 3607685119583216548411549)
        ·
          refine ⟨1352881919843706205654331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3607685119583216548411549 1352881919843706205654331)
          ·
            refine ⟨2029322879765559308481497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352881919843706205654331 2029322879765559308481497)
            ·
              refine ⟨1521992159824169481361123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029322879765559308481497 1521992159824169481361123)
              ·
                refine ⟨2282988239736254222041685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521992159824169481361123 2282988239736254222041685)
                ·
                  refine ⟨26753768434409229164551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2282988239736254222041685 26753768434409229164551)
                  ·
                    rfl

theorem cell23_468925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_468925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468925 prefixEnd_468925 := by exact prefixLift 468925
  have htrace : WordTrace (prefixWord ++ tailWord_468925) baseStart_468925 baseEnd_468925 := by
    simpa [prefixWord, tailWord_468925, baseEnd_468925] using wordTrace_append hprefix tailTrace_468925
  have hstable : (prefixWord ++ tailWord_468925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468925).length < 2 ^ (prefixWord ++ tailWord_468925).sum := by decide
  have hdescent : baseEnd_468925 < baseStart_468925 := by decide
  rcases family_descends (prefixWord ++ tailWord_468925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468952 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_468952 : Nat := 118140960795 + 468952 * 2 ^ 59
def prefixEnd_468952 : Nat := 4983230072969 + 3 ^ 40 * 468952 * 2
def baseEnd_468952 : Nat := 240797779887354456843335

theorem tailTrace_468952 : CollatzResearch.WordTrace tailWord_468952 prefixEnd_468952 240797779887354456843335 := by
  unfold tailWord_468952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552042298537234735184555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11402723064716312980246073 8552042298537234735184555)
  ·
    refine ⟨12828063447805852102776833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552042298537234735184555 12828063447805852102776833)
    ·
      refine ⟨9621047585854389077082625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12828063447805852102776833 9621047585854389077082625)
      ·
        refine ⟨7215785689390791807811969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9621047585854389077082625 7215785689390791807811969)
        ·
          refine ⟨5411839267043093855858977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7215785689390791807811969 5411839267043093855858977)
          ·
            refine ⟨4058879450282320391894233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411839267043093855858977 4058879450282320391894233)
            ·
              refine ⟨3044159587711740293920675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058879450282320391894233 3044159587711740293920675)
              ·
                refine ⟨4566239381567610440881013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044159587711740293920675 4566239381567610440881013)
                ·
                  refine ⟨428084942021963478832595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566239381567610440881013 428084942021963478832595)
                  ·
                    refine ⟨642127413032945218248893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428084942021963478832595 642127413032945218248893)
                    ·
                      refine ⟨240797779887354456843335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642127413032945218248893 240797779887354456843335)
                      ·
                        rfl

theorem cell23_468952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_468952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468952 prefixEnd_468952 := by exact prefixLift 468952
  have htrace : WordTrace (prefixWord ++ tailWord_468952) baseStart_468952 baseEnd_468952 := by
    simpa [prefixWord, tailWord_468952, baseEnd_468952] using wordTrace_append hprefix tailTrace_468952
  have hstable : (prefixWord ++ tailWord_468952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468952).length < 2 ^ (prefixWord ++ tailWord_468952).sum := by decide
  have hdescent : baseEnd_468952 < baseStart_468952 := by decide
  rcases family_descends (prefixWord ++ tailWord_468952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468995 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_468995 : Nat := 118140960795 + 468995 * 2 ^ 59
def prefixEnd_468995 : Nat := 4983230072969 + 3 ^ 40 * 468995 * 2
def baseEnd_468995 : Nat := 240819859555497788605637

theorem tailTrace_468995 : CollatzResearch.WordTrace tailWord_468995 prefixEnd_468995 240819859555497788605637 := by
  unfold tailWord_468995
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105652935918687814184439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11403768623945791876122959 17105652935918687814184439)
  ·
    refine ⟨25658479403878031721276659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17105652935918687814184439 25658479403878031721276659)
    ·
      refine ⟨38487719105817047581914989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25658479403878031721276659 38487719105817047581914989)
      ·
        refine ⟨14432894664681392843218121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38487719105817047581914989 14432894664681392843218121)
        ·
          refine ⟨10824670998511044632413591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14432894664681392843218121 10824670998511044632413591)
          ·
            refine ⟨16237006497766566948620387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10824670998511044632413591 16237006497766566948620387)
            ·
              refine ⟨24355509746649850422930581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16237006497766566948620387 24355509746649850422930581)
              ·
                refine ⟨1141664519374211738574871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24355509746649850422930581 1141664519374211738574871)
                ·
                  refine ⟨1712496779061317607862307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141664519374211738574871 1712496779061317607862307)
                  ·
                    refine ⟨2568745168591976411793461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712496779061317607862307 2568745168591976411793461)
                    ·
                      refine ⟨240819859555497788605637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2568745168591976411793461 240819859555497788605637)
                      ·
                        rfl

theorem cell23_468995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_468995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_468995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_468995 prefixEnd_468995 := by exact prefixLift 468995
  have htrace : WordTrace (prefixWord ++ tailWord_468995) baseStart_468995 baseEnd_468995 := by
    simpa [prefixWord, tailWord_468995, baseEnd_468995] using wordTrace_append hprefix tailTrace_468995
  have hstable : (prefixWord ++ tailWord_468995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468995).length < 2 ^ (prefixWord ++ tailWord_468995).sum := by decide
  have hdescent : baseEnd_468995 < baseStart_468995 := by decide
  rcases family_descends (prefixWord ++ tailWord_468995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469013 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_469013 : Nat := 118140960795 + 469013 * 2 ^ 59
def prefixEnd_469013 : Nat := 4983230072969 + 3 ^ 40 * 469013 * 2
def baseEnd_469013 : Nat := 240829102207278718180555

theorem tailTrace_469013 : CollatzResearch.WordTrace tailWord_469013 prefixEnd_469013 240829102207278718180555 := by
  unfold tailWord_469013
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106309449853476888339693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11404206299902317925559795 17106309449853476888339693)
  ·
    refine ⟨6414866043695053833127385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17106309449853476888339693 6414866043695053833127385)
    ·
      refine ⟨4811149532771290374845539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6414866043695053833127385 4811149532771290374845539)
      ·
        refine ⟨7216724299156935562268309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811149532771290374845539 7216724299156935562268309)
        ·
          refine ⟨338283951522981354481327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7216724299156935562268309 338283951522981354481327)
          ·
            refine ⟨507425927284472031721991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338283951522981354481327 507425927284472031721991)
            ·
              refine ⟨761138890926708047582987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507425927284472031721991 761138890926708047582987)
              ·
                refine ⟨1141708336390062071374481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761138890926708047582987 1141708336390062071374481)
                ·
                  refine ⟨856281252292546553530861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141708336390062071374481 856281252292546553530861)
                  ·
                    refine ⟨321105469609704957574073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 856281252292546553530861 321105469609704957574073)
                    ·
                      refine ⟨240829102207278718180555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 321105469609704957574073 240829102207278718180555)
                      ·
                        rfl

theorem cell23_469013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_469013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469013 prefixEnd_469013 := by exact prefixLift 469013
  have htrace : WordTrace (prefixWord ++ tailWord_469013) baseStart_469013 baseEnd_469013 := by
    simpa [prefixWord, tailWord_469013, baseEnd_469013] using wordTrace_append hprefix tailTrace_469013
  have hstable : (prefixWord ++ tailWord_469013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469013).length < 2 ^ (prefixWord ++ tailWord_469013).sum := by decide
  have hdescent : baseEnd_469013 < baseStart_469013 := by decide
  rcases family_descends (prefixWord ++ tailWord_469013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469029 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_469029 : Nat := 118140960795 + 469029 * 2 ^ 59
def prefixEnd_469029 : Nat := 4983230072969 + 3 ^ 40 * 469029 * 2
def baseEnd_469029 : Nat := 240837317897750655580481

theorem tailTrace_469029 : CollatzResearch.WordTrace tailWord_469029 prefixEnd_469029 240837317897750655580481 := by
  unfold tailWord_469029
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106893017795511620922141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11404595345197007747281427 17106893017795511620922141)
  ·
    refine ⟨6415084881673316857845803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17106893017795511620922141 6415084881673316857845803)
    ·
      refine ⟨9622627322509975286768705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415084881673316857845803 9622627322509975286768705)
      ·
        refine ⟨7216970491882481465076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9622627322509975286768705 7216970491882481465076529)
        ·
          refine ⟨5412727868911861098807397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216970491882481465076529 5412727868911861098807397)
          ·
            refine ⟨1014886475420973956026387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5412727868911861098807397 1014886475420973956026387)
            ·
              refine ⟨1522329713131460934039581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014886475420973956026387 1522329713131460934039581)
              ·
                refine ⟨570873642424297850264843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522329713131460934039581 570873642424297850264843)
                ·
                  refine ⟨856310463636446775397265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570873642424297850264843 856310463636446775397265)
                  ·
                    refine ⟨642232847727335081547949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856310463636446775397265 642232847727335081547949)
                    ·
                      refine ⟨240837317897750655580481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642232847727335081547949 240837317897750655580481)
                      ·
                        rfl

theorem cell23_469029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_469029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469029 prefixEnd_469029 := by exact prefixLift 469029
  have htrace : WordTrace (prefixWord ++ tailWord_469029) baseStart_469029 baseEnd_469029 := by
    simpa [prefixWord, tailWord_469029, baseEnd_469029] using wordTrace_append hprefix tailTrace_469029
  have hstable : (prefixWord ++ tailWord_469029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469029).length < 2 ^ (prefixWord ++ tailWord_469029).sum := by decide
  have hdescent : baseEnd_469029 < baseStart_469029 := by decide
  rcases family_descends (prefixWord ++ tailWord_469029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469045 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_469045 : Nat := 118140960795 + 469045 * 2 ^ 59
def prefixEnd_469045 : Nat := 4983230072969 + 3 ^ 40 * 469045 * 2
def baseEnd_469045 : Nat := 80281844529407530993469

theorem tailTrace_469045 : CollatzResearch.WordTrace tailWord_469045 prefixEnd_469045 80281844529407530993469 := by
  unfold tailWord_469045
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107476585737546353504589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11404984390491697569003059 17107476585737546353504589)
  ·
    refine ⟨6415303719651579882564221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17107476585737546353504589 6415303719651579882564221)
    ·
      refine ⟨2405738894869342455961583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6415303719651579882564221 2405738894869342455961583)
      ·
        refine ⟨3608608342304013683942375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405738894869342455961583 3608608342304013683942375)
        ·
          refine ⟨5412912513456020525913563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608608342304013683942375 5412912513456020525913563)
          ·
            refine ⟨8119368770184030788870345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412912513456020525913563 8119368770184030788870345)
            ·
              refine ⟨6089526577638023091652759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119368770184030788870345 6089526577638023091652759)
              ·
                refine ⟨9134289866457034637479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089526577638023091652759 9134289866457034637479139)
                ·
                  refine ⟨13701434799685551956218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9134289866457034637479139 13701434799685551956218709)
                  ·
                    refine ⟨80281844529407530993469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 13701434799685551956218709 80281844529407530993469)
                    ·
                      rfl

theorem cell23_469045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_469045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469045 prefixEnd_469045 := by exact prefixLift 469045
  have htrace : WordTrace (prefixWord ++ tailWord_469045) baseStart_469045 baseEnd_469045 := by
    simpa [prefixWord, tailWord_469045, baseEnd_469045] using wordTrace_append hprefix tailTrace_469045
  have hstable : (prefixWord ++ tailWord_469045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469045).length < 2 ^ (prefixWord ++ tailWord_469045).sum := by decide
  have hdescent : baseEnd_469045 < baseStart_469045 := by decide
  rcases family_descends (prefixWord ++ tailWord_469045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469102 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_469102 : Nat := 118140960795 + 469102 * 2 ^ 59
def prefixEnd_469102 : Nat := 4983230072969 + 3 ^ 40 * 469102 * 2
def baseEnd_469102 : Nat := 240874801985528869967645

theorem tailTrace_469102 : CollatzResearch.WordTrace tailWord_469102 prefixEnd_469102 240874801985528869967645 := by
  unfold tailWord_469102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138694443316380636041195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11406370364354030058886373 2138694443316380636041195)
  ·
    refine ⟨3208041664974570954061793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138694443316380636041195 3208041664974570954061793)
    ·
      refine ⟨2406031248730928215546345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208041664974570954061793 2406031248730928215546345)
      ·
        refine ⟨1804523436548196161659759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2406031248730928215546345 1804523436548196161659759)
        ·
          refine ⟨2706785154822294242489639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804523436548196161659759 2706785154822294242489639)
          ·
            refine ⟨4060177732233441363734459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706785154822294242489639 4060177732233441363734459)
            ·
              refine ⟨6090266598350162045601689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060177732233441363734459 6090266598350162045601689)
              ·
                refine ⟨4567699948762621534201267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090266598350162045601689 4567699948762621534201267)
                ·
                  refine ⟨6851549923143932301301901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567699948762621534201267 6851549923143932301301901)
                  ·
                    refine ⟨2569331221178974612988213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6851549923143932301301901 2569331221178974612988213)
                    ·
                      refine ⟨240874801985528869967645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2569331221178974612988213 240874801985528869967645)
                      ·
                        rfl

theorem cell23_469102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_469102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469102 prefixEnd_469102 := by exact prefixLift 469102
  have htrace : WordTrace (prefixWord ++ tailWord_469102) baseStart_469102 baseEnd_469102 := by
    simpa [prefixWord, tailWord_469102, baseEnd_469102] using wordTrace_append hprefix tailTrace_469102
  have hstable : (prefixWord ++ tailWord_469102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469102).length < 2 ^ (prefixWord ++ tailWord_469102).sum := by decide
  have hdescent : baseEnd_469102 < baseStart_469102 := by decide
  rcases family_descends (prefixWord ++ tailWord_469102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469110 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_469110 : Nat := 118140960795 + 469110 * 2 ^ 59
def prefixEnd_469110 : Nat := 4983230072969 + 3 ^ 40 * 469110 * 2
def baseEnd_469110 : Nat := 240878909830764838667609

theorem tailTrace_469110 : CollatzResearch.WordTrace tailWord_469110 prefixEnd_469110 240878909830764838667609 := by
  unfold tailWord_469110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069365458156378903413799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11406564887001374969747189 1069365458156378903413799)
  ·
    refine ⟨1604048187234568355120699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1069365458156378903413799 1604048187234568355120699)
    ·
      refine ⟨2406072280851852532681049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604048187234568355120699 2406072280851852532681049)
      ·
        refine ⟨1804554210638889399510787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2406072280851852532681049 1804554210638889399510787)
        ·
          refine ⟨2706831315958334099266181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804554210638889399510787 2706831315958334099266181)
          ·
            refine ⟨507530871742187643612409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2706831315958334099266181 507530871742187643612409)
            ·
              refine ⟨380648153806640732709307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507530871742187643612409 380648153806640732709307)
              ·
                refine ⟨570972230709961099063961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380648153806640732709307 570972230709961099063961)
                ·
                  refine ⟨428229173032470824297971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570972230709961099063961 428229173032470824297971)
                  ·
                    refine ⟨642343759548706236446957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428229173032470824297971 642343759548706236446957)
                    ·
                      refine ⟨240878909830764838667609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642343759548706236446957 240878909830764838667609)
                      ·
                        rfl

theorem cell23_469110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_469110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469110 prefixEnd_469110 := by exact prefixLift 469110
  have htrace : WordTrace (prefixWord ++ tailWord_469110) baseStart_469110 baseEnd_469110 := by
    simpa [prefixWord, tailWord_469110, baseEnd_469110] using wordTrace_append hprefix tailTrace_469110
  have hstable : (prefixWord ++ tailWord_469110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469110).length < 2 ^ (prefixWord ++ tailWord_469110).sum := by decide
  have hdescent : baseEnd_469110 < baseStart_469110 := by decide
  rcases family_descends (prefixWord ++ tailWord_469110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469132 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_469132 : Nat := 118140960795 + 469132 * 2 ^ 59
def prefixEnd_469132 : Nat := 4983230072969 + 3 ^ 40 * 469132 * 2
def baseEnd_469132 : Nat := 240890206405163752592507

theorem tailTrace_469132 : CollatzResearch.WordTrace tailWord_469132 prefixEnd_469132 240890206405163752592507 := by
  unfold tailWord_469132
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555324868211180105960825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11407099824281573474614433 8555324868211180105960825)
  ·
    refine ⟨6416493651158385079470619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8555324868211180105960825 6416493651158385079470619)
    ·
      refine ⟨9624740476737577619205929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416493651158385079470619 9624740476737577619205929)
      ·
        refine ⟨7218555357553183214404447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9624740476737577619205929 7218555357553183214404447)
        ·
          refine ⟨10827833036329774821606671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218555357553183214404447 10827833036329774821606671)
          ·
            refine ⟨16241749554494662232410007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10827833036329774821606671 16241749554494662232410007)
            ·
              refine ⟨24362624331741993348615011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16241749554494662232410007 24362624331741993348615011)
              ·
                refine ⟨36543936497612990022922517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24362624331741993348615011 36543936497612990022922517)
                ·
                  refine ⟨1712997023325608907324493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36543936497612990022922517 1712997023325608907324493)
                  ·
                    refine ⟨642373883747103340246685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1712997023325608907324493 642373883747103340246685)
                    ·
                      refine ⟨240890206405163752592507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 642373883747103340246685 240890206405163752592507)
                      ·
                        rfl

theorem cell23_469132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_469132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469132 prefixEnd_469132 := by exact prefixLift 469132
  have htrace : WordTrace (prefixWord ++ tailWord_469132) baseStart_469132 baseEnd_469132 := by
    simpa [prefixWord, tailWord_469132, baseEnd_469132] using wordTrace_append hprefix tailTrace_469132
  have hstable : (prefixWord ++ tailWord_469132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469132).length < 2 ^ (prefixWord ++ tailWord_469132).sum := by decide
  have hdescent : baseEnd_469132 < baseStart_469132 := by decide
  rcases family_descends (prefixWord ++ tailWord_469132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469156 : List Nat := [2, 3, 1, 2, 4, 1, 1, 4, 5]
def baseStart_469156 : Nat := 118140960795 + 469156 * 2 ^ 59
def prefixEnd_469156 : Nat := 4983230072969 + 3 ^ 40 * 469156 * 2
def baseEnd_469156 : Nat := 26766947771207962076933

theorem tailTrace_469156 : CollatzResearch.WordTrace tailWord_469156 prefixEnd_469156 26766947771207962076933 := by
  unfold tailWord_469156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555762544167706155397661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11407683392223608207196881 8555762544167706155397661)
  ·
    refine ⟨3208410954062889808274123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8555762544167706155397661 3208410954062889808274123)
    ·
      refine ⟨4812616431094334712411185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208410954062889808274123 4812616431094334712411185)
      ·
        refine ⟨3609462323320751034308389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4812616431094334712411185 3609462323320751034308389)
        ·
          refine ⟨676774185622640818932823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3609462323320751034308389 676774185622640818932823)
          ·
            refine ⟨1015161278433961228399235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676774185622640818932823 1015161278433961228399235)
            ·
              refine ⟨1522741917650941842598853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015161278433961228399235 1522741917650941842598853)
              ·
                refine ⟨285514109559551595487285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1522741917650941842598853 285514109559551595487285)
                ·
                  refine ⟨26766947771207962076933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285514109559551595487285 26766947771207962076933)
                  ·
                    rfl

theorem cell23_469156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_469156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_469156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_469156 prefixEnd_469156 := by exact prefixLift 469156
  have htrace : WordTrace (prefixWord ++ tailWord_469156) baseStart_469156 baseEnd_469156 := by
    simpa [prefixWord, tailWord_469156, baseEnd_469156] using wordTrace_append hprefix tailTrace_469156
  have hstable : (prefixWord ++ tailWord_469156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469156).length < 2 ^ (prefixWord ++ tailWord_469156).sum := by decide
  have hdescent : baseEnd_469156 < baseStart_469156 := by decide
  rcases family_descends (prefixWord ++ tailWord_469156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
