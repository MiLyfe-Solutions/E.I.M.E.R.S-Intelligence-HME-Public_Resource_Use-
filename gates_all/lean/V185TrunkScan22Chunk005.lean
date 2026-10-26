import V185TrunkScan22Chunk004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_44249 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_44249 : Nat := 118140960795 + 44249 * 2 ^ 59
def prefixEnd_44249 : Nat := 4983230072969 + 3 ^ 40 * 44249 * 2
def baseEnd_44249 : Nat := 15147336987268406189339

theorem tailTrace_44249 : CollatzResearch.WordTrace tailWord_44249 prefixEnd_44249 15147336987268406189339 := by
  unfold tailWord_44249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613893616700904972655801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075929077800603315103867 1613893616700904972655801)
  ·
    refine ⟨1210420212525678729491851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1613893616700904972655801 1210420212525678729491851)
    ·
      refine ⟨1815630318788518094237777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210420212525678729491851 1815630318788518094237777)
      ·
        refine ⟨1361722739091388570678333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815630318788518094237777 1361722739091388570678333)
        ·
          refine ⟨510646027159270714004375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1361722739091388570678333 510646027159270714004375)
          ·
            refine ⟨765969040738906071006563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510646027159270714004375 765969040738906071006563)
            ·
              refine ⟨1148953561108359106509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765969040738906071006563 1148953561108359106509845)
              ·
                refine ⟨53857198176954333117649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1148953561108359106509845 53857198176954333117649)
                ·
                  refine ⟨40392898632715749838237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53857198176954333117649 40392898632715749838237)
                  ·
                    refine ⟨15147336987268406189339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40392898632715749838237 15147336987268406189339)
                    ·
                      rfl

theorem cell22_44249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_44249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44249 prefixEnd_44249 := by exact prefixLift 44249
  have htrace : WordTrace (prefixWord ++ tailWord_44249) baseStart_44249 baseEnd_44249 := by
    simpa [prefixWord, tailWord_44249, baseEnd_44249] using wordTrace_append hprefix tailTrace_44249
  have hstable : (prefixWord ++ tailWord_44249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44249).length < 2 ^ (prefixWord ++ tailWord_44249).sum := by decide
  have hdescent : baseEnd_44249 < baseStart_44249 := by decide
  rcases family_descends (prefixWord ++ tailWord_44249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44266 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_44266 : Nat := 118140960795 + 44266 * 2 ^ 59
def prefixEnd_44266 : Nat := 4983230072969 + 3 ^ 40 * 44266 * 2
def baseEnd_44266 : Nat := 15153156434686028514287

theorem tailTrace_44266 : CollatzResearch.WordTrace tailWord_44266 prefixEnd_44266 15153156434686028514287 := by
  unfold tailWord_44266
  simp only [CollatzResearch.WordTrace]
  refine ⟨403628414409829219006163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1076342438426211250683101 403628414409829219006163)
  ·
    refine ⟨605442621614743828509245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403628414409829219006163 605442621614743828509245)
    ·
      refine ⟨227040983105528935690967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 605442621614743828509245 227040983105528935690967)
      ·
        refine ⟨340561474658293403536451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227040983105528935690967 340561474658293403536451)
        ·
          refine ⟨510842211987440105304677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340561474658293403536451 510842211987440105304677)
          ·
            refine ⟨95782914747645019744627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510842211987440105304677 95782914747645019744627)
            ·
              refine ⟨143674372121467529616941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95782914747645019744627 143674372121467529616941)
              ·
                refine ⟨53877889545550323606353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143674372121467529616941 53877889545550323606353)
                ·
                  refine ⟨40408417159162742704765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53877889545550323606353 40408417159162742704765)
                  ·
                    refine ⟨15153156434686028514287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40408417159162742704765 15153156434686028514287)
                    ·
                      rfl

theorem cell22_44266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_44266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44266 prefixEnd_44266 := by exact prefixLift 44266
  have htrace : WordTrace (prefixWord ++ tailWord_44266) baseStart_44266 baseEnd_44266 := by
    simpa [prefixWord, tailWord_44266, baseEnd_44266] using wordTrace_append hprefix tailTrace_44266
  have hstable : (prefixWord ++ tailWord_44266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44266).length < 2 ^ (prefixWord ++ tailWord_44266).sum := by decide
  have hdescent : baseEnd_44266 < baseStart_44266 := by decide
  rcases family_descends (prefixWord ++ tailWord_44266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44324 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_44324 : Nat := 118140960795 + 44324 * 2 ^ 59
def prefixEnd_44324 : Nat := 4983230072969 + 3 ^ 40 * 44324 * 2
def baseEnd_44324 : Nat := 5057670339997736854703

theorem tailTrace_44324 : CollatzResearch.WordTrace tailWord_44324 prefixEnd_44324 5057670339997736854703 := by
  unfold tailWord_44324
  simp only [CollatzResearch.WordTrace]
  refine ⟨808314545714596390818013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1077752727619461854424017 808314545714596390818013)
  ·
    refine ⟨303117954642973646556755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 808314545714596390818013 303117954642973646556755)
    ·
      refine ⟨454676931964460469835133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303117954642973646556755 454676931964460469835133)
      ·
        refine ⟨170503849486672676188175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 454676931964460469835133 170503849486672676188175)
        ·
          refine ⟨255755774230009014282263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170503849486672676188175 255755774230009014282263)
          ·
            refine ⟨383633661345013521423395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255755774230009014282263 383633661345013521423395)
            ·
              refine ⟨575450492017520282135093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383633661345013521423395 575450492017520282135093)
              ·
                refine ⟨53948483626642526450165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 575450492017520282135093 53948483626642526450165)
                ·
                  refine ⟨5057670339997736854703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53948483626642526450165 5057670339997736854703)
                  ·
                    rfl

theorem cell22_44324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_44324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44324 prefixEnd_44324 := by exact prefixLift 44324
  have htrace : WordTrace (prefixWord ++ tailWord_44324) baseStart_44324 baseEnd_44324 := by
    simpa [prefixWord, tailWord_44324, baseEnd_44324] using wordTrace_append hprefix tailTrace_44324
  have hstable : (prefixWord ++ tailWord_44324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44324).length < 2 ^ (prefixWord ++ tailWord_44324).sum := by decide
  have hdescent : baseEnd_44324 < baseStart_44324 := by decide
  rcases family_descends (prefixWord ++ tailWord_44324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44345 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_44345 : Nat := 118140960795 + 44345 * 2 ^ 59
def prefixEnd_44345 : Nat := 4983230072969 + 3 ^ 40 * 44345 * 2
def baseEnd_44345 : Nat := 15180199749156155789045

theorem tailTrace_44345 : CollatzResearch.WordTrace tailWord_44345 prefixEnd_44345 15180199749156155789045 := by
  unfold tailWord_44345
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617395024353113368150489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1078263349568742245433659 1617395024353113368150489)
  ·
    refine ⟨1213046268264835026112867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1617395024353113368150489 1213046268264835026112867)
    ·
      refine ⟨1819569402397252539169301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213046268264835026112867 1819569402397252539169301)
      ·
        refine ⟨85292315737371212773561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1819569402397252539169301 85292315737371212773561)
        ·
          refine ⟨63969236803028409580171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85292315737371212773561 63969236803028409580171)
          ·
            refine ⟨95953855204542614370257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63969236803028409580171 95953855204542614370257)
            ·
              refine ⟨71965391403406960777693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95953855204542614370257 71965391403406960777693)
              ·
                refine ⟨26987021776277610291635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71965391403406960777693 26987021776277610291635)
                ·
                  refine ⟨40480532664416415437453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26987021776277610291635 40480532664416415437453)
                  ·
                    refine ⟨15180199749156155789045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40480532664416415437453 15180199749156155789045)
                    ·
                      rfl

theorem cell22_44345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_44345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44345 prefixEnd_44345 := by exact prefixLift 44345
  have htrace : WordTrace (prefixWord ++ tailWord_44345) baseStart_44345 baseEnd_44345 := by
    simpa [prefixWord, tailWord_44345, baseEnd_44345] using wordTrace_append hprefix tailTrace_44345
  have hstable : (prefixWord ++ tailWord_44345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44345).length < 2 ^ (prefixWord ++ tailWord_44345).sum := by decide
  have hdescent : baseEnd_44345 < baseStart_44345 := by decide
  rcases family_descends (prefixWord ++ tailWord_44345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44352 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 8]
def baseStart_44352 : Nat := 118140960795 + 44352 * 2 ^ 59
def prefixEnd_44352 : Nat := 4983230072969 + 3 ^ 40 * 44352 * 2
def baseEnd_44352 : Nat := 5060865330736823621341

theorem tailTrace_44352 : CollatzResearch.WordTrace tailWord_44352 prefixEnd_44352 5060865330736823621341 := by
  unfold tailWord_44352
  simp only [CollatzResearch.WordTrace]
  refine ⟨808825167663876781827655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1078433556885169042436873 808825167663876781827655)
  ·
    refine ⟨1213237751495815172741483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 808825167663876781827655 1213237751495815172741483)
    ·
      refine ⟨1819856627243722759112225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213237751495815172741483 1819856627243722759112225)
      ·
        refine ⟨1364892470432792069334169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1819856627243722759112225 1364892470432792069334169)
        ·
          refine ⟨1023669352824594052000627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1364892470432792069334169 1023669352824594052000627)
          ·
            refine ⟨1535504029236891078000941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023669352824594052000627 1535504029236891078000941)
            ·
              refine ⟨575814010963834154250353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1535504029236891078000941 575814010963834154250353)
              ·
                refine ⟨431860508222875615687765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575814010963834154250353 431860508222875615687765)
                ·
                  refine ⟨5060865330736823621341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 431860508222875615687765 5060865330736823621341)
                  ·
                    rfl

theorem cell22_44352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_44352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44352 prefixEnd_44352 := by exact prefixLift 44352
  have htrace : WordTrace (prefixWord ++ tailWord_44352) baseStart_44352 baseEnd_44352 := by
    simpa [prefixWord, tailWord_44352, baseEnd_44352] using wordTrace_append hprefix tailTrace_44352
  have hstable : (prefixWord ++ tailWord_44352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44352).length < 2 ^ (prefixWord ++ tailWord_44352).sum := by decide
  have hdescent : baseEnd_44352 < baseStart_44352 := by decide
  rcases family_descends (prefixWord ++ tailWord_44352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44356 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_44356 : Nat := 118140960795 + 44356 * 2 ^ 59
def prefixEnd_44356 : Nat := 4983230072969 + 3 ^ 40 * 44356 * 2
def baseEnd_44356 : Nat := 15183965273955793764011

theorem tailTrace_44356 : CollatzResearch.WordTrace tailWord_44356 prefixEnd_44356 15183965273955793764011 := by
  unfold tailWord_44356
  simp only [CollatzResearch.WordTrace]
  refine ⟨808898113656631123400461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1078530818208841497867281 808898113656631123400461)
  ·
    refine ⟨303336792621236671275173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 808898113656631123400461 303336792621236671275173)
    ·
      refine ⟨56875648616481875864095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303336792621236671275173 56875648616481875864095)
      ·
        refine ⟨85313472924722813796143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56875648616481875864095 85313472924722813796143)
        ·
          refine ⟨127970209387084220694215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85313472924722813796143 127970209387084220694215)
          ·
            refine ⟨191955314080626331041323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127970209387084220694215 191955314080626331041323)
            ·
              refine ⟨287932971120939496561985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191955314080626331041323 287932971120939496561985)
              ·
                refine ⟨215949728340704622421489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287932971120939496561985 215949728340704622421489)
                ·
                  refine ⟨161962296255528466816117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215949728340704622421489 161962296255528466816117)
                  ·
                    refine ⟨15183965273955793764011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161962296255528466816117 15183965273955793764011)
                    ·
                      rfl

theorem cell22_44356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_44356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44356 prefixEnd_44356 := by exact prefixLift 44356
  have htrace : WordTrace (prefixWord ++ tailWord_44356) baseStart_44356 baseEnd_44356 := by
    simpa [prefixWord, tailWord_44356, baseEnd_44356] using wordTrace_append hprefix tailTrace_44356
  have hstable : (prefixWord ++ tailWord_44356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44356).length < 2 ^ (prefixWord ++ tailWord_44356).sum := by decide
  have hdescent : baseEnd_44356 < baseStart_44356 := by decide
  rcases family_descends (prefixWord ++ tailWord_44356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44369 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 6]
def baseStart_44369 : Nat := 118140960795 + 44369 * 2 ^ 59
def prefixEnd_44369 : Nat := 4983230072969 + 3 ^ 40 * 44369 * 2
def baseEnd_44369 : Nat := 5062805146542697729657

theorem tailTrace_44369 : CollatzResearch.WordTrace tailWord_44369 prefixEnd_44369 5062805146542697729657 := by
  unfold tailWord_44369
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618270376266165467024161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1078846917510776978016107 1618270376266165467024161)
  ·
    refine ⟨1213702782199624100268121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1618270376266165467024161 1213702782199624100268121)
    ·
      refine ⟨910277086649718075201091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1213702782199624100268121 910277086649718075201091)
      ·
        refine ⟨1365415629974577112801637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910277086649718075201091 1365415629974577112801637)
        ·
          refine ⟨256015430620233208650307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1365415629974577112801637 256015430620233208650307)
          ·
            refine ⟨384023145930349812975461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256015430620233208650307 384023145930349812975461)
            ·
              refine ⟨72004339861940589932899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384023145930349812975461 72004339861940589932899)
              ·
                refine ⟨108006509792910884899349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72004339861940589932899 108006509792910884899349)
                ·
                  refine ⟨5062805146542697729657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108006509792910884899349 5062805146542697729657)
                  ·
                    rfl

theorem cell22_44369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_44369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44369 prefixEnd_44369 := by exact prefixLift 44369
  have htrace : WordTrace (prefixWord ++ tailWord_44369) baseStart_44369 baseEnd_44369 := by
    simpa [prefixWord, tailWord_44369, baseEnd_44369] using wordTrace_append hprefix tailTrace_44369
  have hstable : (prefixWord ++ tailWord_44369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44369).length < 2 ^ (prefixWord ++ tailWord_44369).sum := by decide
  have hdescent : baseEnd_44369 < baseStart_44369 := by decide
  rcases family_descends (prefixWord ++ tailWord_44369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44399 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_44399 : Nat := 118140960795 + 44399 * 2 ^ 59
def prefixEnd_44399 : Nat := 4983230072969 + 3 ^ 40 * 44399 * 2
def baseEnd_44399 : Nat := 15198685052718014938879

theorem tailTrace_44399 : CollatzResearch.WordTrace tailWord_44399 prefixEnd_44399 15198685052718014938879 := by
  unfold tailWord_44399
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619364566157480590616251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1079576377438320393744167 1619364566157480590616251)
  ·
    refine ⟨2429046849236220885924377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619364566157480590616251 2429046849236220885924377)
    ·
      refine ⟨1821785136927165664443283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2429046849236220885924377 1821785136927165664443283)
      ·
        refine ⟨2732677705390748496664925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821785136927165664443283 2732677705390748496664925)
        ·
          refine ⟨1024754139521530686249347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2732677705390748496664925 1024754139521530686249347)
          ·
            refine ⟨1537131209282296029374021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024754139521530686249347 1537131209282296029374021)
            ·
              refine ⟨288212101740430505507629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1537131209282296029374021 288212101740430505507629)
              ·
                refine ⟨108079538152661439565361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288212101740430505507629 108079538152661439565361)
                ·
                  refine ⟨81059653614496079674021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108079538152661439565361 81059653614496079674021)
                  ·
                    refine ⟨15198685052718014938879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81059653614496079674021 15198685052718014938879)
                    ·
                      rfl

theorem cell22_44399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_44399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44399 prefixEnd_44399 := by exact prefixLift 44399
  have htrace : WordTrace (prefixWord ++ tailWord_44399) baseStart_44399 baseEnd_44399 := by
    simpa [prefixWord, tailWord_44399, baseEnd_44399] using wordTrace_append hprefix tailTrace_44399
  have hstable : (prefixWord ++ tailWord_44399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44399).length < 2 ^ (prefixWord ++ tailWord_44399).sum := by decide
  have hdescent : baseEnd_44399 < baseStart_44399 := by decide
  rcases family_descends (prefixWord ++ tailWord_44399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44480 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_44480 : Nat := 118140960795 + 44480 * 2 ^ 59
def prefixEnd_44480 : Nat := 4983230072969 + 3 ^ 40 * 44480 * 2
def baseEnd_44480 : Nat := 15226413008060803663631

theorem tailTrace_44480 : CollatzResearch.WordTrace tailWord_44480 prefixEnd_44480 15226413008060803663631 := by
  unfold tailWord_44480
  simp only [CollatzResearch.WordTrace]
  refine ⟨811159439432015712157447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1081545919242687616209929 811159439432015712157447)
  ·
    refine ⟨1216739159148023568236171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811159439432015712157447 1216739159148023568236171)
    ·
      refine ⟨1825108738722035352354257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216739159148023568236171 1825108738722035352354257)
      ·
        refine ⟨1368831554041526514265693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825108738722035352354257 1368831554041526514265693)
        ·
          refine ⟨513311832765572442849635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1368831554041526514265693 513311832765572442849635)
          ·
            refine ⟨769967749148358664274453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513311832765572442849635 769967749148358664274453)
            ·
              refine ⟨36092238241329312387865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 769967749148358664274453 36092238241329312387865)
              ·
                refine ⟨27069178680996984290899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36092238241329312387865 27069178680996984290899)
                ·
                  refine ⟨40603768021495476436349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27069178680996984290899 40603768021495476436349)
                  ·
                    refine ⟨15226413008060803663631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40603768021495476436349 15226413008060803663631)
                    ·
                      rfl

theorem cell22_44480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_44480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44480 prefixEnd_44480 := by exact prefixLift 44480
  have htrace : WordTrace (prefixWord ++ tailWord_44480) baseStart_44480 baseEnd_44480 := by
    simpa [prefixWord, tailWord_44480, baseEnd_44480] using wordTrace_append hprefix tailTrace_44480
  have hstable : (prefixWord ++ tailWord_44480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44480).length < 2 ^ (prefixWord ++ tailWord_44480).sum := by decide
  have hdescent : baseEnd_44480 < baseStart_44480 := by decide
  rcases family_descends (prefixWord ++ tailWord_44480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44504 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_44504 : Nat := 118140960795 + 44504 * 2 ^ 59
def prefixEnd_44504 : Nat := 4983230072969 + 3 ^ 40 * 44504 * 2
def baseEnd_44504 : Nat := 5078209566177580354519

theorem tailTrace_44504 : CollatzResearch.WordTrace tailWord_44504 prefixEnd_44504 5078209566177580354519 := by
  unfold tailWord_44504
  simp only [CollatzResearch.WordTrace]
  refine ⟨811597115388541761594283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1082129487184722348792377 811597115388541761594283)
  ·
    refine ⟨1217395673082812642391425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811597115388541761594283 1217395673082812642391425)
    ·
      refine ⟨913046754812109481793569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1217395673082812642391425 913046754812109481793569)
      ·
        refine ⟨684785066109082111345177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913046754812109481793569 684785066109082111345177)
        ·
          refine ⟨513588799581811583508883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684785066109082111345177 513588799581811583508883)
          ·
            refine ⟨770383199372717375263325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513588799581811583508883 770383199372717375263325)
            ·
              refine ⟨288893699764769015723747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 770383199372717375263325 288893699764769015723747)
              ·
                refine ⟨433340549647153523585621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288893699764769015723747 433340549647153523585621)
                ·
                  refine ⟨5078209566177580354519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 433340549647153523585621 5078209566177580354519)
                  ·
                    rfl

theorem cell22_44504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_44504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44504 prefixEnd_44504 := by exact prefixLift 44504
  have htrace : WordTrace (prefixWord ++ tailWord_44504) baseStart_44504 baseEnd_44504 := by
    simpa [prefixWord, tailWord_44504, baseEnd_44504] using wordTrace_append hprefix tailTrace_44504
  have hstable : (prefixWord ++ tailWord_44504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44504).length < 2 ^ (prefixWord ++ tailWord_44504).sum := by decide
  have hdescent : baseEnd_44504 < baseStart_44504 := by decide
  rcases family_descends (prefixWord ++ tailWord_44504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44506 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_44506 : Nat := 118140960795 + 44506 * 2 ^ 59
def prefixEnd_44506 : Nat := 4983230072969 + 3 ^ 40 * 44506 * 2
def baseEnd_44506 : Nat := 15235313339405402513551

theorem tailTrace_44506 : CollatzResearch.WordTrace tailWord_44506 prefixEnd_44506 15235313339405402513551 := by
  unfold tailWord_44506
  simp only [CollatzResearch.WordTrace]
  refine ⟨405816794192459466190343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1082178117846558576507581 405816794192459466190343)
  ·
    refine ⟨608725191288689199285515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405816794192459466190343 608725191288689199285515)
    ·
      refine ⟨913087786933033798928273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608725191288689199285515 913087786933033798928273)
      ·
        refine ⟨684815840199775349196205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913087786933033798928273 684815840199775349196205)
        ·
          refine ⟨256805940074915755948577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684815840199775349196205 256805940074915755948577)
          ·
            refine ⟨192604455056186816961433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256805940074915755948577 192604455056186816961433)
            ·
              refine ⟨144453341292140112721075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192604455056186816961433 144453341292140112721075)
              ·
                refine ⟨216680011938210169081613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144453341292140112721075 216680011938210169081613)
                ·
                  refine ⟨81255004476828813405605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216680011938210169081613 81255004476828813405605)
                  ·
                    refine ⟨15235313339405402513551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81255004476828813405605 15235313339405402513551)
                    ·
                      rfl

theorem cell22_44506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_44506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44506 prefixEnd_44506 := by exact prefixLift 44506
  have htrace : WordTrace (prefixWord ++ tailWord_44506) baseStart_44506 baseEnd_44506 := by
    simpa [prefixWord, tailWord_44506, baseEnd_44506] using wordTrace_append hprefix tailTrace_44506
  have hstable : (prefixWord ++ tailWord_44506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44506).length < 2 ^ (prefixWord ++ tailWord_44506).sum := by decide
  have hdescent : baseEnd_44506 < baseStart_44506 := by decide
  rcases family_descends (prefixWord ++ tailWord_44506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44549 : List Nat := [1, 3, 1, 1, 2, 2, 1, 11]
def baseStart_44549 : Nat := 118140960795 + 44549 * 2 ^ 59
def prefixEnd_44549 : Nat := 4983230072969 + 3 ^ 40 * 44549 * 2
def baseEnd_44549 : Nat := 1694448124240847076491

theorem tailTrace_44549 : CollatzResearch.WordTrace tailWord_44549 prefixEnd_44549 1694448124240847076491 := by
  unfold tailWord_44549
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624835515614056208576701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083223677076037472384467 1624835515614056208576701)
  ·
    refine ⟨609313318355271078216263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1624835515614056208576701 609313318355271078216263)
    ·
      refine ⟨913969977532906617324395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609313318355271078216263 913969977532906617324395)
      ·
        refine ⟨1370954966299359925986593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913969977532906617324395 1370954966299359925986593)
        ·
          refine ⟨1028216224724519944489945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370954966299359925986593 1028216224724519944489945)
          ·
            refine ⟨771162168543389958367459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028216224724519944489945 771162168543389958367459)
            ·
              refine ⟨1156743252815084937551189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771162168543389958367459 1156743252815084937551189)
              ·
                refine ⟨1694448124240847076491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1156743252815084937551189 1694448124240847076491)
                ·
                  rfl

theorem cell22_44549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 11].length) (baseStart_44549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44549 prefixEnd_44549 := by exact prefixLift 44549
  have htrace : WordTrace (prefixWord ++ tailWord_44549) baseStart_44549 baseEnd_44549 := by
    simpa [prefixWord, tailWord_44549, baseEnd_44549] using wordTrace_append hprefix tailTrace_44549
  have hstable : (prefixWord ++ tailWord_44549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44549).length < 2 ^ (prefixWord ++ tailWord_44549).sum := by decide
  have hdescent : baseEnd_44549 < baseStart_44549 := by decide
  rcases family_descends (prefixWord ++ tailWord_44549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44551 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_44551 : Nat := 118140960795 + 44551 * 2 ^ 59
def prefixEnd_44551 : Nat := 4983230072969 + 3 ^ 40 * 44551 * 2
def baseEnd_44551 : Nat := 15250717759040285138413

theorem tailTrace_44551 : CollatzResearch.WordTrace tailWord_44551 prefixEnd_44551 15250717759040285138413 := by
  unfold tailWord_44551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624908461606810550149507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083272307737873700099671 1624908461606810550149507)
  ·
    refine ⟨2437362692410215825224261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624908461606810550149507 2437362692410215825224261)
    ·
      refine ⟨457005504826915467229549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2437362692410215825224261 457005504826915467229549)
      ·
        refine ⟨171377064310093300211081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457005504826915467229549 171377064310093300211081)
        ·
          refine ⟨128532798232569975158311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171377064310093300211081 128532798232569975158311)
          ·
            refine ⟨192799197348854962737467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128532798232569975158311 192799197348854962737467)
            ·
              refine ⟨289198796023282444106201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192799197348854962737467 289198796023282444106201)
              ·
                refine ⟨216899097017461833079651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289198796023282444106201 216899097017461833079651)
                ·
                  refine ⟨325348645526192749619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216899097017461833079651 325348645526192749619477)
                  ·
                    refine ⟨15250717759040285138413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 325348645526192749619477 15250717759040285138413)
                    ·
                      rfl

theorem cell22_44551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_44551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44551 prefixEnd_44551 := by exact prefixLift 44551
  have htrace : WordTrace (prefixWord ++ tailWord_44551) baseStart_44551 baseEnd_44551 := by
    simpa [prefixWord, tailWord_44551, baseEnd_44551] using wordTrace_append hprefix tailTrace_44551
  have hstable : (prefixWord ++ tailWord_44551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44551).length < 2 ^ (prefixWord ++ tailWord_44551).sum := by decide
  have hdescent : baseEnd_44551 < baseStart_44551 := by decide
  rcases family_descends (prefixWord ++ tailWord_44551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44604 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_44604 : Nat := 118140960795 + 44604 * 2 ^ 59
def prefixEnd_44604 : Nat := 4983230072969 + 3 ^ 40 * 44604 * 2
def baseEnd_44604 : Nat := 15268860742165813563251

theorem tailTrace_44604 : CollatzResearch.WordTrace tailWord_44604 prefixEnd_44604 15268860742165813563251 := by
  unfold tailWord_44604
  simp only [CollatzResearch.WordTrace]
  refine ⟨813420765207400300914433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1084561020276533734552577 813420765207400300914433)
  ·
    refine ⟨610065573905550225685825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 813420765207400300914433 610065573905550225685825)
    ·
      refine ⟨457549180429162669264369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 610065573905550225685825 457549180429162669264369)
      ·
        refine ⟨343161885321872001948277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457549180429162669264369 343161885321872001948277)
        ·
          refine ⟨32171426748925500182651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343161885321872001948277 32171426748925500182651)
          ·
            refine ⟨48257140123388250273977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32171426748925500182651 48257140123388250273977)
            ·
              refine ⟨36192855092541187705483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48257140123388250273977 36192855092541187705483)
              ·
                refine ⟨54289282638811781558225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36192855092541187705483 54289282638811781558225)
                ·
                  refine ⟨40716961979108836168669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54289282638811781558225 40716961979108836168669)
                  ·
                    refine ⟨15268860742165813563251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40716961979108836168669 15268860742165813563251)
                    ·
                      rfl

theorem cell22_44604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_44604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44604 prefixEnd_44604 := by exact prefixLift 44604
  have htrace : WordTrace (prefixWord ++ tailWord_44604) baseStart_44604 baseEnd_44604 := by
    simpa [prefixWord, tailWord_44604, baseEnd_44604] using wordTrace_append hprefix tailTrace_44604
  have hstable : (prefixWord ++ tailWord_44604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44604).length < 2 ^ (prefixWord ++ tailWord_44604).sum := by decide
  have hdescent : baseEnd_44604 < baseStart_44604 := by decide
  rcases family_descends (prefixWord ++ tailWord_44604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44658 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_44658 : Nat := 118140960795 + 44658 * 2 ^ 59
def prefixEnd_44658 : Nat := 4983230072969 + 3 ^ 40 * 44658 * 2
def baseEnd_44658 : Nat := 15287346045727672713085

theorem tailTrace_44658 : CollatzResearch.WordTrace tailWord_44658 prefixEnd_44658 15287346045727672713085 := by
  unfold tailWord_44658
  simp only [CollatzResearch.WordTrace]
  refine ⟨407202768054791956073657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1085874048146111882863085 407202768054791956073657)
  ·
    refine ⟨305402076041093967055243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 407202768054791956073657 305402076041093967055243)
    ·
      refine ⟨458103114061640950582865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305402076041093967055243 458103114061640950582865)
      ·
        refine ⟨343577335546230712937149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458103114061640950582865 343577335546230712937149)
        ·
          refine ⟨128841500829836517351431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343577335546230712937149 128841500829836517351431)
          ·
            refine ⟨193262251244754776027147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128841500829836517351431 193262251244754776027147)
            ·
              refine ⟨289893376867132164040721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193262251244754776027147 289893376867132164040721)
              ·
                refine ⟨217420032650349123030541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289893376867132164040721 217420032650349123030541)
                ·
                  refine ⟨81532512243880921136453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217420032650349123030541 81532512243880921136453)
                  ·
                    refine ⟨15287346045727672713085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81532512243880921136453 15287346045727672713085)
                    ·
                      rfl

theorem cell22_44658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_44658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44658 prefixEnd_44658 := by exact prefixLift 44658
  have htrace : WordTrace (prefixWord ++ tailWord_44658) baseStart_44658 baseEnd_44658 := by
    simpa [prefixWord, tailWord_44658, baseEnd_44658] using wordTrace_append hprefix tailTrace_44658
  have hstable : (prefixWord ++ tailWord_44658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44658).length < 2 ^ (prefixWord ++ tailWord_44658).sum := by decide
  have hdescent : baseEnd_44658 < baseStart_44658 := by decide
  rcases family_descends (prefixWord ++ tailWord_44658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44673 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 6]
def baseStart_44673 : Nat := 118140960795 + 44673 * 2 ^ 59
def prefixEnd_44673 : Nat := 4983230072969 + 3 ^ 40 * 44673 * 2
def baseEnd_44673 : Nat := 5097493617424211196013

theorem tailTrace_44673 : CollatzResearch.WordTrace tailWord_44673 prefixEnd_44673 5097493617424211196013 := by
  unfold tailWord_44673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629358167164825386090673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1086238778109883590727115 1629358167164825386090673)
  ·
    refine ⟨1222018625373619039568005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629358167164825386090673 1222018625373619039568005)
    ·
      refine ⟨229128492257553569919001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1222018625373619039568005 229128492257553569919001)
      ·
        refine ⟨171846369193165177439251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229128492257553569919001 171846369193165177439251)
        ·
          refine ⟨257769553789747766158877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171846369193165177439251 257769553789747766158877)
          ·
            refine ⟨96663582671155412309579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257769553789747766158877 96663582671155412309579)
            ·
              refine ⟨144995374006733118464369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96663582671155412309579 144995374006733118464369)
              ·
                refine ⟨108746530505049838848277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144995374006733118464369 108746530505049838848277)
                ·
                  refine ⟨5097493617424211196013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108746530505049838848277 5097493617424211196013)
                  ·
                    rfl

theorem cell22_44673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_44673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44673 prefixEnd_44673 := by exact prefixLift 44673
  have htrace : WordTrace (prefixWord ++ tailWord_44673) baseStart_44673 baseEnd_44673 := by
    simpa [prefixWord, tailWord_44673, baseEnd_44673] using wordTrace_append hprefix tailTrace_44673
  have hstable : (prefixWord ++ tailWord_44673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44673).length < 2 ^ (prefixWord ++ tailWord_44673).sum := by decide
  have hdescent : baseEnd_44673 < baseStart_44673 := by decide
  rcases family_descends (prefixWord ++ tailWord_44673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44692 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_44692 : Nat := 118140960795 + 44692 * 2 ^ 59
def prefixEnd_44692 : Nat := 4983230072969 + 3 ^ 40 * 44692 * 2
def baseEnd_44692 : Nat := 15298984940562917362981

theorem tailTrace_44692 : CollatzResearch.WordTrace tailWord_44692 prefixEnd_44692 15298984940562917362981 := by
  unfold tailWord_44692
  simp only [CollatzResearch.WordTrace]
  refine ⟨815025577047995815516165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1086700769397327754021553 815025577047995815516165)
  ·
    refine ⟨152817295696499215409281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 815025577047995815516165 152817295696499215409281)
    ·
      refine ⟨114612971772374411556961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152817295696499215409281 114612971772374411556961)
      ·
        refine ⟨85959728829280808667721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114612971772374411556961 85959728829280808667721)
        ·
          refine ⟨64469796621960606500791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85959728829280808667721 64469796621960606500791)
          ·
            refine ⟨96704694932940909751187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64469796621960606500791 96704694932940909751187)
            ·
              refine ⟨145057042399411364626781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96704694932940909751187 145057042399411364626781)
              ·
                refine ⟨54396390899779261735043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145057042399411364626781 54396390899779261735043)
                ·
                  refine ⟨81594586349668892602565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54396390899779261735043 81594586349668892602565)
                  ·
                    refine ⟨15298984940562917362981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81594586349668892602565 15298984940562917362981)
                    ·
                      rfl

theorem cell22_44692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_44692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44692 prefixEnd_44692 := by exact prefixLift 44692
  have htrace : WordTrace (prefixWord ++ tailWord_44692) baseStart_44692 baseEnd_44692 := by
    simpa [prefixWord, tailWord_44692, baseEnd_44692] using wordTrace_append hprefix tailTrace_44692
  have hstable : (prefixWord ++ tailWord_44692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44692).length < 2 ^ (prefixWord ++ tailWord_44692).sum := by decide
  have hdescent : baseEnd_44692 < baseStart_44692 := by decide
  rcases family_descends (prefixWord ++ tailWord_44692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44705 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_44705 : Nat := 118140960795 + 44705 * 2 ^ 59
def prefixEnd_44705 : Nat := 4983230072969 + 3 ^ 40 * 44705 * 2
def baseEnd_44705 : Nat := 15303435106235216787941

theorem tailTrace_44705 : CollatzResearch.WordTrace tailWord_44705 prefixEnd_44705 15303435106235216787941 := by
  unfold tailWord_44705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630525303048894851255569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1087016868699263234170379 1630525303048894851255569)
  ·
    refine ⟨1222893977286671138441677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1630525303048894851255569 1222893977286671138441677)
    ·
      refine ⟨458585241482501676915629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1222893977286671138441677 458585241482501676915629)
      ·
        refine ⟨171969465555938128843361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 458585241482501676915629 171969465555938128843361)
        ·
          refine ⟨128977099166953596632521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171969465555938128843361 128977099166953596632521)
          ·
            refine ⟨96732824375215197474391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128977099166953596632521 96732824375215197474391)
            ·
              refine ⟨145099236562822796211587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96732824375215197474391 145099236562822796211587)
              ·
                refine ⟨217648854844234194317381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145099236562822796211587 217648854844234194317381)
                ·
                  refine ⟨40809160283293911434509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217648854844234194317381 40809160283293911434509)
                  ·
                    refine ⟨15303435106235216787941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40809160283293911434509 15303435106235216787941)
                    ·
                      rfl

theorem cell22_44705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_44705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44705 prefixEnd_44705 := by exact prefixLift 44705
  have htrace : WordTrace (prefixWord ++ tailWord_44705) baseStart_44705 baseEnd_44705 := by
    simpa [prefixWord, tailWord_44705, baseEnd_44705] using wordTrace_append hprefix tailTrace_44705
  have hstable : (prefixWord ++ tailWord_44705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44705).length < 2 ^ (prefixWord ++ tailWord_44705).sum := by decide
  have hdescent : baseEnd_44705 < baseStart_44705 := by decide
  rcases family_descends (prefixWord ++ tailWord_44705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44731 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_44731 : Nat := 118140960795 + 44731 * 2 ^ 59
def prefixEnd_44731 : Nat := 4983230072969 + 3 ^ 40 * 44731 * 2
def baseEnd_44731 : Nat := 15312335437579815637861

theorem tailTrace_44731 : CollatzResearch.WordTrace tailWord_44731 prefixEnd_44731 15312335437579815637861 := by
  unfold tailWord_44731
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631473600954701291702047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1087649067303134194468031 1631473600954701291702047)
  ·
    refine ⟨2447210401432051937553071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631473600954701291702047 2447210401432051937553071)
    ·
      refine ⟨3670815602148077906329607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447210401432051937553071 3670815602148077906329607)
      ·
        refine ⟨5506223403222116859494411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670815602148077906329607 5506223403222116859494411)
        ·
          refine ⟨8259335104833175289241617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506223403222116859494411 8259335104833175289241617)
          ·
            refine ⟨6194501328624881466931213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259335104833175289241617 6194501328624881466931213)
            ·
              refine ⟨2322937998234330550099205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6194501328624881466931213 2322937998234330550099205)
              ·
                refine ⟨435550874668936978143601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2322937998234330550099205 435550874668936978143601)
                ·
                  refine ⟨326663156001702733607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 435550874668936978143601 326663156001702733607701)
                  ·
                    refine ⟨15312335437579815637861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 326663156001702733607701 15312335437579815637861)
                    ·
                      rfl

theorem cell22_44731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_44731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44731 prefixEnd_44731 := by exact prefixLift 44731
  have htrace : WordTrace (prefixWord ++ tailWord_44731) baseStart_44731 baseEnd_44731 := by
    simpa [prefixWord, tailWord_44731, baseEnd_44731] using wordTrace_append hprefix tailTrace_44731
  have hstable : (prefixWord ++ tailWord_44731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44731).length < 2 ^ (prefixWord ++ tailWord_44731).sum := by decide
  have hdescent : baseEnd_44731 < baseStart_44731 := by decide
  rcases family_descends (prefixWord ++ tailWord_44731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44778 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_44778 : Nat := 118140960795 + 44778 * 2 ^ 59
def prefixEnd_44778 : Nat := 4983230072969 + 3 ^ 40 * 44778 * 2
def baseEnd_44778 : Nat := 15328424498087359712717

theorem tailTrace_44778 : CollatzResearch.WordTrace tailWord_44778 prefixEnd_44778 15328424498087359712717 := by
  unfold tailWord_44778
  simp only [CollatzResearch.WordTrace]
  refine ⟨408296957946107079665747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1088791887856285545775325 408296957946107079665747)
  ·
    refine ⟨612445436919160619498621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408296957946107079665747 612445436919160619498621)
    ·
      refine ⟨229667038844685232311983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 612445436919160619498621 229667038844685232311983)
      ·
        refine ⟨344500558267027848467975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229667038844685232311983 344500558267027848467975)
        ·
          refine ⟨516750837400541772701963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344500558267027848467975 516750837400541772701963)
          ·
            refine ⟨775126256100812659052945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516750837400541772701963 775126256100812659052945)
            ·
              refine ⟨581344692075609494289709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775126256100812659052945 581344692075609494289709)
              ·
                refine ⟨218004259528353560358641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581344692075609494289709 218004259528353560358641)
                ·
                  refine ⟨163503194646265170268981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218004259528353560358641 163503194646265170268981)
                  ·
                    refine ⟨15328424498087359712717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163503194646265170268981 15328424498087359712717)
                    ·
                      rfl

theorem cell22_44778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_44778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44778 prefixEnd_44778 := by exact prefixLift 44778
  have htrace : WordTrace (prefixWord ++ tailWord_44778) baseStart_44778 baseEnd_44778 := by
    simpa [prefixWord, tailWord_44778, baseEnd_44778] using wordTrace_append hprefix tailTrace_44778
  have hstable : (prefixWord ++ tailWord_44778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44778).length < 2 ^ (prefixWord ++ tailWord_44778).sum := by decide
  have hdescent : baseEnd_44778 < baseStart_44778 := by decide
  rcases family_descends (prefixWord ++ tailWord_44778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44780 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_44780 : Nat := 118140960795 + 44780 * 2 ^ 59
def prefixEnd_44780 : Nat := 4983230072969 + 3 ^ 40 * 44780 * 2
def baseEnd_44780 : Nat := 5109703046320007054237

theorem tailTrace_44780 : CollatzResearch.WordTrace tailWord_44780 prefixEnd_44780 5109703046320007054237 := by
  unfold tailWord_44780
  simp only [CollatzResearch.WordTrace]
  refine ⟨816630388888591330117897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088840518518121773490529 816630388888591330117897)
  ·
    refine ⟨612472791666443497588423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816630388888591330117897 612472791666443497588423)
    ·
      refine ⟨918709187499665246382635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612472791666443497588423 918709187499665246382635)
      ·
        refine ⟨1378063781249497869573953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918709187499665246382635 1378063781249497869573953)
        ·
          refine ⟨1033547835937123402180465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378063781249497869573953 1033547835937123402180465)
          ·
            refine ⟨775160876952842551635349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033547835937123402180465 775160876952842551635349)
            ·
              refine ⟨36335666107164494607907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 775160876952842551635349 36335666107164494607907)
              ·
                refine ⟨54503499160746741911861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36335666107164494607907 54503499160746741911861)
                ·
                  refine ⟨5109703046320007054237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54503499160746741911861 5109703046320007054237)
                  ·
                    rfl

theorem cell22_44780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_44780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44780 prefixEnd_44780 := by exact prefixLift 44780
  have htrace : WordTrace (prefixWord ++ tailWord_44780) baseStart_44780 baseEnd_44780 := by
    simpa [prefixWord, tailWord_44780, baseEnd_44780] using wordTrace_append hprefix tailTrace_44780
  have hstable : (prefixWord ++ tailWord_44780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44780).length < 2 ^ (prefixWord ++ tailWord_44780).sum := by decide
  have hdescent : baseEnd_44780 < baseStart_44780 := by decide
  rcases family_descends (prefixWord ++ tailWord_44780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44818 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_44818 : Nat := 118140960795 + 44818 * 2 ^ 59
def prefixEnd_44818 : Nat := 4983230072969 + 3 ^ 40 * 44818 * 2
def baseEnd_44818 : Nat := 15342117315540588712595

theorem tailTrace_44818 : CollatzResearch.WordTrace tailWord_44818 prefixEnd_44818 15342117315540588712595 := by
  unfold tailWord_44818
  simp only [CollatzResearch.WordTrace]
  refine ⟨408661687909878787529777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1089764501093010100079405 408661687909878787529777)
  ·
    refine ⟨306496265932409090647333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 408661687909878787529777 306496265932409090647333)
    ·
      refine ⟨57468049862326704496375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306496265932409090647333 57468049862326704496375)
      ·
        refine ⟨86202074793490056744563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57468049862326704496375 86202074793490056744563)
        ·
          refine ⟨129303112190235085116845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86202074793490056744563 129303112190235085116845)
          ·
            refine ⟨48488667071338156918817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129303112190235085116845 48488667071338156918817)
            ·
              refine ⟨36366500303503617689113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48488667071338156918817 36366500303503617689113)
              ·
                refine ⟨27274875227627713266835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36366500303503617689113 27274875227627713266835)
                ·
                  refine ⟨40912312841441569900253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27274875227627713266835 40912312841441569900253)
                  ·
                    refine ⟨15342117315540588712595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40912312841441569900253 15342117315540588712595)
                    ·
                      rfl

theorem cell22_44818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_44818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44818 prefixEnd_44818 := by exact prefixLift 44818
  have htrace : WordTrace (prefixWord ++ tailWord_44818) baseStart_44818 baseEnd_44818 := by
    simpa [prefixWord, tailWord_44818, baseEnd_44818] using wordTrace_append hprefix tailTrace_44818
  have hstable : (prefixWord ++ tailWord_44818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44818).length < 2 ^ (prefixWord ++ tailWord_44818).sum := by decide
  have hdescent : baseEnd_44818 < baseStart_44818 := by decide
  rcases family_descends (prefixWord ++ tailWord_44818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44840 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_44840 : Nat := 118140960795 + 44840 * 2 ^ 59
def prefixEnd_44840 : Nat := 4983230072969 + 3 ^ 40 * 44840 * 2
def baseEnd_44840 : Nat := 15349648365139864662527

theorem tailTrace_44840 : CollatzResearch.WordTrace tailWord_44840 prefixEnd_44840 15349648365139864662527 := by
  unfold tailWord_44840
  simp only [CollatzResearch.WordTrace]
  refine ⟨817724578779906453709987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1090299438373208604946649 817724578779906453709987)
  ·
    refine ⟨1226586868169859680564981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 817724578779906453709987 1226586868169859680564981)
    ·
      refine ⟨114992518890924345052967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1226586868169859680564981 114992518890924345052967)
      ·
        refine ⟨172488778336386517579451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114992518890924345052967 172488778336386517579451)
        ·
          refine ⟨258733167504579776369177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172488778336386517579451 258733167504579776369177)
          ·
            refine ⟨194049875628434832276883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258733167504579776369177 194049875628434832276883)
            ·
              refine ⟨291074813442652248415325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194049875628434832276883 291074813442652248415325)
              ·
                refine ⟨109153055040994593155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291074813442652248415325 109153055040994593155747)
                ·
                  refine ⟨163729582561491889733621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109153055040994593155747 163729582561491889733621)
                  ·
                    refine ⟨15349648365139864662527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163729582561491889733621 15349648365139864662527)
                    ·
                      rfl

theorem cell22_44840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_44840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44840 prefixEnd_44840 := by exact prefixLift 44840
  have htrace : WordTrace (prefixWord ++ tailWord_44840) baseStart_44840 baseEnd_44840 := by
    simpa [prefixWord, tailWord_44840, baseEnd_44840] using wordTrace_append hprefix tailTrace_44840
  have hstable : (prefixWord ++ tailWord_44840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44840).length < 2 ^ (prefixWord ++ tailWord_44840).sum := by decide
  have hdescent : baseEnd_44840 < baseStart_44840 := by decide
  rcases family_descends (prefixWord ++ tailWord_44840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44936 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_44936 : Nat := 118140960795 + 44936 * 2 ^ 59
def prefixEnd_44936 : Nat := 4983230072969 + 3 ^ 40 * 44936 * 2
def baseEnd_44936 : Nat := 15382511127027614262233

theorem tailTrace_44936 : CollatzResearch.WordTrace tailWord_44936 prefixEnd_44936 15382511127027614262233 := by
  unfold tailWord_44936
  simp only [CollatzResearch.WordTrace]
  refine ⟨819475282606010651457331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1092633710141347535276441 819475282606010651457331)
  ·
    refine ⟨1229212923909015977185997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819475282606010651457331 1229212923909015977185997)
    ·
      refine ⟨460954846465880991444749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1229212923909015977185997 460954846465880991444749)
      ·
        refine ⟨172858067424705371791781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460954846465880991444749 172858067424705371791781)
        ·
          refine ⟨32410887642132257210959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172858067424705371791781 32410887642132257210959)
          ·
            refine ⟨48616331463198385816439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32410887642132257210959 48616331463198385816439)
            ·
              refine ⟨72924497194797578724659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48616331463198385816439 72924497194797578724659)
              ·
                refine ⟨109386745792196368086989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72924497194797578724659 109386745792196368086989)
                ·
                  refine ⟨41020029672073638032621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109386745792196368086989 41020029672073638032621)
                  ·
                    refine ⟨15382511127027614262233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41020029672073638032621 15382511127027614262233)
                    ·
                      rfl

theorem cell22_44936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_44936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44936 prefixEnd_44936 := by exact prefixLift 44936
  have htrace : WordTrace (prefixWord ++ tailWord_44936) baseStart_44936 baseEnd_44936 := by
    simpa [prefixWord, tailWord_44936, baseEnd_44936] using wordTrace_append hprefix tailTrace_44936
  have hstable : (prefixWord ++ tailWord_44936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44936).length < 2 ^ (prefixWord ++ tailWord_44936).sum := by decide
  have hdescent : baseEnd_44936 < baseStart_44936 := by decide
  rcases family_descends (prefixWord ++ tailWord_44936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44975 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_44975 : Nat := 118140960795 + 44975 * 2 ^ 59
def prefixEnd_44975 : Nat := 4983230072969 + 3 ^ 40 * 44975 * 2
def baseEnd_44975 : Nat := 15395861624044512537113

theorem tailTrace_44975 : CollatzResearch.WordTrace tailWord_44975 prefixEnd_44975 15395861624044512537113 := by
  unfold tailWord_44975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640373012070730963584379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1093582008047153975722919 1640373012070730963584379)
  ·
    refine ⟨2460559518106096445376569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640373012070730963584379 2460559518106096445376569)
    ·
      refine ⟨1845419638579572334032427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460559518106096445376569 1845419638579572334032427)
      ·
        refine ⟨2768129457869358501048641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845419638579572334032427 2768129457869358501048641)
        ·
          refine ⟨2076097093402018875786481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2768129457869358501048641 2076097093402018875786481)
          ·
            refine ⟨1557072820051514156839861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076097093402018875786481 1557072820051514156839861)
            ·
              refine ⟨145975576879829452203737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1557072820051514156839861 145975576879829452203737)
              ·
                refine ⟨109481682659872089152803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145975576879829452203737 109481682659872089152803)
                ·
                  refine ⟨164222523989808133729205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109481682659872089152803 164222523989808133729205)
                  ·
                    refine ⟨15395861624044512537113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 164222523989808133729205 15395861624044512537113)
                    ·
                      rfl

theorem cell22_44975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_44975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_44975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_44975 prefixEnd_44975 := by exact prefixLift 44975
  have htrace : WordTrace (prefixWord ++ tailWord_44975) baseStart_44975 baseEnd_44975 := by
    simpa [prefixWord, tailWord_44975, baseEnd_44975] using wordTrace_append hprefix tailTrace_44975
  have hstable : (prefixWord ++ tailWord_44975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44975).length < 2 ^ (prefixWord ++ tailWord_44975).sum := by decide
  have hdescent : baseEnd_44975 < baseStart_44975 := by decide
  rcases family_descends (prefixWord ++ tailWord_44975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45118 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_45118 : Nat := 118140960795 + 45118 * 2 ^ 59
def prefixEnd_45118 : Nat := 4983230072969 + 3 ^ 40 * 45118 * 2
def baseEnd_45118 : Nat := 5148271148813268737225

theorem tailTrace_45118 : CollatzResearch.WordTrace tailWord_45118 prefixEnd_45118 5148271148813268737225 := by
  unfold tailWord_45118
  simp only [CollatzResearch.WordTrace]
  refine ⟨205698581319083298255001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1097059100368444257360005 205698581319083298255001)
  ·
    refine ⟨154273935989312473691251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205698581319083298255001 154273935989312473691251)
    ·
      refine ⟨231410903983968710536877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154273935989312473691251 231410903983968710536877)
      ·
        refine ⟨86779088993988266451329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231410903983968710536877 86779088993988266451329)
        ·
          refine ⟨65084316745491199838497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86779088993988266451329 65084316745491199838497)
          ·
            refine ⟨48813237559118399878873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65084316745491199838497 48813237559118399878873)
            ·
              refine ⟨36609928169338799909155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48813237559118399878873 36609928169338799909155)
              ·
                refine ⟨54914892254008199863733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36609928169338799909155 54914892254008199863733)
                ·
                  refine ⟨5148271148813268737225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54914892254008199863733 5148271148813268737225)
                  ·
                    rfl

theorem cell22_45118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_45118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45118 prefixEnd_45118 := by exact prefixLift 45118
  have htrace : WordTrace (prefixWord ++ tailWord_45118) baseStart_45118 baseEnd_45118 := by
    simpa [prefixWord, tailWord_45118, baseEnd_45118] using wordTrace_append hprefix tailTrace_45118
  have hstable : (prefixWord ++ tailWord_45118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45118).length < 2 ^ (prefixWord ++ tailWord_45118).sum := by decide
  have hdescent : baseEnd_45118 < baseStart_45118 := by decide
  rcases family_descends (prefixWord ++ tailWord_45118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45127 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_45127 : Nat := 118140960795 + 45127 * 2 ^ 59
def prefixEnd_45127 : Nat := 4983230072969 + 3 ^ 40 * 45127 * 2
def baseEnd_45127 : Nat := 15447894330366782736647

theorem tailTrace_45127 : CollatzResearch.WordTrace tailWord_45127 prefixEnd_45127 15447894330366782736647 := by
  unfold tailWord_45127
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645916907520060923117635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1097277938346707282078423 1645916907520060923117635)
  ·
    refine ⟨2468875361280091384676453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645916907520060923117635 2468875361280091384676453)
    ·
      refine ⟨462914130240017134626835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2468875361280091384676453 462914130240017134626835)
      ·
        refine ⟨694371195360025701940253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462914130240017134626835 694371195360025701940253)
        ·
          refine ⟨260389198260009638227595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 694371195360025701940253 260389198260009638227595)
          ·
            refine ⟨390583797390014457341393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260389198260009638227595 390583797390014457341393)
            ·
              refine ⟨292937848042510843006045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390583797390014457341393 292937848042510843006045)
              ·
                refine ⟨109851693015941566127267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292937848042510843006045 109851693015941566127267)
                ·
                  refine ⟨164777539523912349190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109851693015941566127267 164777539523912349190901)
                  ·
                    refine ⟨15447894330366782736647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 164777539523912349190901 15447894330366782736647)
                    ·
                      rfl

theorem cell22_45127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_45127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45127 prefixEnd_45127 := by exact prefixLift 45127
  have htrace : WordTrace (prefixWord ++ tailWord_45127) baseStart_45127 baseEnd_45127 := by
    simpa [prefixWord, tailWord_45127, baseEnd_45127] using wordTrace_append hprefix tailTrace_45127
  have hstable : (prefixWord ++ tailWord_45127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45127).length < 2 ^ (prefixWord ++ tailWord_45127).sum := by decide
  have hdescent : baseEnd_45127 < baseStart_45127 := by decide
  rcases family_descends (prefixWord ++ tailWord_45127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45174 : List Nat := [5, 1, 1, 2, 1, 2, 3, 7]
def baseStart_45174 : Nat := 118140960795 + 45174 * 2 ^ 59
def prefixEnd_45174 : Nat := 4983230072969 + 3 ^ 40 * 45174 * 2
def baseEnd_45174 : Nat := 1718220376763814090167

theorem tailTrace_45174 : CollatzResearch.WordTrace tailWord_45174 prefixEnd_45174 1718220376763814090167 := by
  unfold tailWord_45174
  simp only [CollatzResearch.WordTrace]
  refine ⟨102976946146861746879911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1098420758899858633385717 102976946146861746879911)
  ·
    refine ⟨154465419220292620319867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102976946146861746879911 154465419220292620319867)
    ·
      refine ⟨231698128830438930479801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154465419220292620319867 231698128830438930479801)
      ·
        refine ⟨173773596622829197859851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231698128830438930479801 173773596622829197859851)
        ·
          refine ⟨260660394934243796789777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173773596622829197859851 260660394934243796789777)
          ·
            refine ⟨195495296200682847592333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260660394934243796789777 195495296200682847592333)
            ·
              refine ⟨73310736075256067847125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195495296200682847592333 73310736075256067847125)
              ·
                refine ⟨1718220376763814090167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73310736075256067847125 1718220376763814090167)
                ·
                  rfl

theorem cell22_45174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_45174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45174 prefixEnd_45174 := by exact prefixLift 45174
  have htrace : WordTrace (prefixWord ++ tailWord_45174) baseStart_45174 baseEnd_45174 := by
    simpa [prefixWord, tailWord_45174, baseEnd_45174] using wordTrace_append hprefix tailTrace_45174
  have hstable : (prefixWord ++ tailWord_45174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45174).length < 2 ^ (prefixWord ++ tailWord_45174).sum := by decide
  have hdescent : baseEnd_45174 < baseStart_45174 := by decide
  rcases family_descends (prefixWord ++ tailWord_45174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45189 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 5, 3]
def baseStart_45189 : Nat := 118140960795 + 45189 * 2 ^ 59
def prefixEnd_45189 : Nat := 4983230072969 + 3 ^ 40 * 45189 * 2
def baseEnd_45189 : Nat := 15469118197419287686457

theorem tailTrace_45189 : CollatzResearch.WordTrace tailWord_45189 prefixEnd_45189 15469118197419287686457 := by
  unfold tailWord_45189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648178233295445511874621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1098785488863630341249747 1648178233295445511874621)
  ·
    refine ⟨618066837485792066952983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1648178233295445511874621 618066837485792066952983)
    ·
      refine ⟨927100256228688100429475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618066837485792066952983 927100256228688100429475)
      ·
        refine ⟨1390650384343032150644213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927100256228688100429475 1390650384343032150644213)
        ·
          refine ⟨130373473532159264122895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1390650384343032150644213 130373473532159264122895)
          ·
            refine ⟨195560210298238896184343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130373473532159264122895 195560210298238896184343)
            ·
              refine ⟨293340315447358344276515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195560210298238896184343 293340315447358344276515)
              ·
                refine ⟨440010473171037516414773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293340315447358344276515 440010473171037516414773)
                ·
                  refine ⟨41250981859784767163885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 440010473171037516414773 41250981859784767163885)
                  ·
                    refine ⟨15469118197419287686457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41250981859784767163885 15469118197419287686457)
                    ·
                      rfl

theorem cell22_45189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_45189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45189 prefixEnd_45189 := by exact prefixLift 45189
  have htrace : WordTrace (prefixWord ++ tailWord_45189) baseStart_45189 baseEnd_45189 := by
    simpa [prefixWord, tailWord_45189, baseEnd_45189] using wordTrace_append hprefix tailTrace_45189
  have hstable : (prefixWord ++ tailWord_45189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45189).length < 2 ^ (prefixWord ++ tailWord_45189).sum := by decide
  have hdescent : baseEnd_45189 < baseStart_45189 := by decide
  rcases family_descends (prefixWord ++ tailWord_45189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45223 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 3, 3]
def baseStart_45223 : Nat := 118140960795 + 45223 * 2 ^ 59
def prefixEnd_45223 : Nat := 4983230072969 + 3 ^ 40 * 45223 * 2
def baseEnd_45223 : Nat := 15480757092254532336353

theorem tailTrace_45223 : CollatzResearch.WordTrace tailWord_45223 prefixEnd_45223 15480757092254532336353 := by
  unfold tailWord_45223
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649418315172269318612323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1099612210114846212408215 1649418315172269318612323)
  ·
    refine ⟨2474127472758403977918485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649418315172269318612323 2474127472758403977918485)
    ·
      refine ⟨115974725285550186464929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2474127472758403977918485 115974725285550186464929)
      ·
        refine ⟨86981043964162639848697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115974725285550186464929 86981043964162639848697)
        ·
          refine ⟨65235782973121979886523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86981043964162639848697 65235782973121979886523)
          ·
            refine ⟨97853674459682969829785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65235782973121979886523 97853674459682969829785)
            ·
              refine ⟨73390255844762227372339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97853674459682969829785 73390255844762227372339)
              ·
                refine ⟨110085383767143341058509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73390255844762227372339 110085383767143341058509)
                ·
                  refine ⟨41282018912678752896941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110085383767143341058509 41282018912678752896941)
                  ·
                    refine ⟨15480757092254532336353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41282018912678752896941 15480757092254532336353)
                    ·
                      rfl

theorem cell22_45223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_45223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45223 prefixEnd_45223 := by exact prefixLift 45223
  have htrace : WordTrace (prefixWord ++ tailWord_45223) baseStart_45223 baseEnd_45223 := by
    simpa [prefixWord, tailWord_45223, baseEnd_45223] using wordTrace_append hprefix tailTrace_45223
  have hstable : (prefixWord ++ tailWord_45223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45223).length < 2 ^ (prefixWord ++ tailWord_45223).sum := by decide
  have hdescent : baseEnd_45223 < baseStart_45223 := by decide
  rcases family_descends (prefixWord ++ tailWord_45223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45266 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_45266 : Nat := 118140960795 + 45266 * 2 ^ 59
def prefixEnd_45266 : Nat := 4983230072969 + 3 ^ 40 * 45266 * 2
def baseEnd_45266 : Nat := 15495476871016753511221

theorem tailTrace_45266 : CollatzResearch.WordTrace tailWord_45266 prefixEnd_45266 15495476871016753511221 := by
  unfold tailWord_45266
  simp only [CollatzResearch.WordTrace]
  refine ⟨412746663504121915606913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1100657769344325108285101 412746663504121915606913)
  ·
    refine ⟨309559997628091436705185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412746663504121915606913 309559997628091436705185)
    ·
      refine ⟨232169998221068577528889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309559997628091436705185 232169998221068577528889)
      ·
        refine ⟨174127498665801433146667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232169998221068577528889 174127498665801433146667)
        ·
          refine ⟨261191247998702149720001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174127498665801433146667 261191247998702149720001)
          ·
            refine ⟨195893435999026612290001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261191247998702149720001 195893435999026612290001)
            ·
              refine ⟨146920076999269959217501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195893435999026612290001 146920076999269959217501)
              ·
                refine ⟨55095028874726234706563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146920076999269959217501 55095028874726234706563)
                ·
                  refine ⟨82642543312089352059845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55095028874726234706563 82642543312089352059845)
                  ·
                    refine ⟨15495476871016753511221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82642543312089352059845 15495476871016753511221)
                    ·
                      rfl

theorem cell22_45266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_45266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45266 prefixEnd_45266 := by exact prefixLift 45266
  have htrace : WordTrace (prefixWord ++ tailWord_45266) baseStart_45266 baseEnd_45266 := by
    simpa [prefixWord, tailWord_45266, baseEnd_45266] using wordTrace_append hprefix tailTrace_45266
  have hstable : (prefixWord ++ tailWord_45266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45266).length < 2 ^ (prefixWord ++ tailWord_45266).sum := by decide
  have hdescent : baseEnd_45266 < baseStart_45266 := by decide
  rcases family_descends (prefixWord ++ tailWord_45266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45294 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_45294 : Nat := 118140960795 + 45294 * 2 ^ 59
def prefixEnd_45294 : Nat := 4983230072969 + 3 ^ 40 * 45294 * 2
def baseEnd_45294 : Nat := 15505061843234013811135

theorem tailTrace_45294 : CollatzResearch.WordTrace tailWord_45294 prefixEnd_45294 15505061843234013811135 := by
  unfold tailWord_45294
  simp only [CollatzResearch.WordTrace]
  refine ⟨206500987239381055555867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1101338598610032296297957 206500987239381055555867)
  ·
    refine ⟨309751480859071583333801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206500987239381055555867 309751480859071583333801)
    ·
      refine ⟨232313610644303687500351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309751480859071583333801 232313610644303687500351)
      ·
        refine ⟨348470415966455531250527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232313610644303687500351 348470415966455531250527)
        ·
          refine ⟨522705623949683296875791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348470415966455531250527 522705623949683296875791)
          ·
            refine ⟨784058435924524945313687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522705623949683296875791 784058435924524945313687)
            ·
              refine ⟨1176087653886787417970531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784058435924524945313687 1176087653886787417970531)
              ·
                refine ⟨1764131480830181126955797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176087653886787417970531 1764131480830181126955797)
                ·
                  refine ⟨82693663163914740326053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1764131480830181126955797 82693663163914740326053)
                  ·
                    refine ⟨15505061843234013811135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82693663163914740326053 15505061843234013811135)
                    ·
                      rfl

theorem cell22_45294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_45294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45294 prefixEnd_45294 := by exact prefixLift 45294
  have htrace : WordTrace (prefixWord ++ tailWord_45294) baseStart_45294 baseEnd_45294 := by
    simpa [prefixWord, tailWord_45294, baseEnd_45294] using wordTrace_append hprefix tailTrace_45294
  have hstable : (prefixWord ++ tailWord_45294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45294).length < 2 ^ (prefixWord ++ tailWord_45294).sum := by decide
  have hdescent : baseEnd_45294 < baseStart_45294 := by decide
  rcases family_descends (prefixWord ++ tailWord_45294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45416 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_45416 : Nat := 118140960795 + 45416 * 2 ^ 59
def prefixEnd_45416 : Nat := 4983230072969 + 3 ^ 40 * 45416 * 2
def baseEnd_45416 : Nat := 5182274978822120753587

theorem tailTrace_45416 : CollatzResearch.WordTrace tailWord_45416 prefixEnd_45416 5182274978822120753587 := by
  unfold tailWord_45416
  simp only [CollatzResearch.WordTrace]
  refine ⟨828228801736531640194051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1104305068982042186925401 828228801736531640194051)
  ·
    refine ⟨1242343202604797460291077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828228801736531640194051 1242343202604797460291077)
    ·
      refine ⟨232939350488399523804577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1242343202604797460291077 232939350488399523804577)
      ·
        refine ⟨174704512866299642853433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232939350488399523804577 174704512866299642853433)
        ·
          refine ⟨131028384649724732140075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174704512866299642853433 131028384649724732140075)
          ·
            refine ⟨196542576974587098210113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131028384649724732140075 196542576974587098210113)
            ·
              refine ⟨147406932730940323657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196542576974587098210113 147406932730940323657585)
              ·
                refine ⟨110555199548205242743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147406932730940323657585 110555199548205242743189)
                ·
                  refine ⟨5182274978822120753587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110555199548205242743189 5182274978822120753587)
                  ·
                    rfl

theorem cell22_45416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_45416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45416 prefixEnd_45416 := by exact prefixLift 45416
  have htrace : WordTrace (prefixWord ++ tailWord_45416) baseStart_45416 baseEnd_45416 := by
    simpa [prefixWord, tailWord_45416, baseEnd_45416] using wordTrace_append hprefix tailTrace_45416
  have hstable : (prefixWord ++ tailWord_45416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45416).length < 2 ^ (prefixWord ++ tailWord_45416).sum := by decide
  have hdescent : baseEnd_45416 < baseStart_45416 := by decide
  rcases family_descends (prefixWord ++ tailWord_45416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45418 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_45418 : Nat := 118140960795 + 45418 * 2 ^ 59
def prefixEnd_45418 : Nat := 4983230072969 + 3 ^ 40 * 45418 * 2
def baseEnd_45418 : Nat := 15547509577339023710755

theorem tailTrace_45418 : CollatzResearch.WordTrace tailWord_45418 prefixEnd_45418 15547509577339023710755 := by
  unfold tailWord_45418
  simp only [CollatzResearch.WordTrace]
  refine ⟨414132637366454405490227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1104353699643878414640605 414132637366454405490227)
  ·
    refine ⟨621198956049681608235341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414132637366454405490227 621198956049681608235341)
    ·
      refine ⟨232949608518630603088253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 621198956049681608235341 232949608518630603088253)
      ·
        refine ⟨87356103194486476158095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232949608518630603088253 87356103194486476158095)
        ·
          refine ⟨131034154791729714237143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87356103194486476158095 131034154791729714237143)
          ·
            refine ⟨196551232187594571355715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131034154791729714237143 196551232187594571355715)
            ·
              refine ⟨294826848281391857033573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196551232187594571355715 294826848281391857033573)
              ·
                refine ⟨55280034052760973193795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294826848281391857033573 55280034052760973193795)
                ·
                  refine ⟨82920051079141459790693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55280034052760973193795 82920051079141459790693)
                  ·
                    refine ⟨15547509577339023710755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82920051079141459790693 15547509577339023710755)
                    ·
                      rfl

theorem cell22_45418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_45418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45418 prefixEnd_45418 := by exact prefixLift 45418
  have htrace : WordTrace (prefixWord ++ tailWord_45418) baseStart_45418 baseEnd_45418 := by
    simpa [prefixWord, tailWord_45418, baseEnd_45418] using wordTrace_append hprefix tailTrace_45418
  have hstable : (prefixWord ++ tailWord_45418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45418).length < 2 ^ (prefixWord ++ tailWord_45418).sum := by decide
  have hdescent : baseEnd_45418 < baseStart_45418 := by decide
  rcases family_descends (prefixWord ++ tailWord_45418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45448 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_45448 : Nat := 118140960795 + 45448 * 2 ^ 59
def prefixEnd_45448 : Nat := 4983230072969 + 3 ^ 40 * 45448 * 2
def baseEnd_45448 : Nat := 15557779190428945460663

theorem tailTrace_45448 : CollatzResearch.WordTrace tailWord_45448 prefixEnd_45448 15557779190428945460663 := by
  unfold tailWord_45448
  simp only [CollatzResearch.WordTrace]
  refine ⟨828812369678566372776499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1105083159571421830368665 828812369678566372776499)
  ·
    refine ⟨1243218554517849559164749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828812369678566372776499 1243218554517849559164749)
    ·
      refine ⟨466206957944193584686781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1243218554517849559164749 466206957944193584686781)
      ·
        refine ⟨174827609229072594257543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466206957944193584686781 174827609229072594257543)
        ·
          refine ⟨262241413843608891386315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174827609229072594257543 262241413843608891386315)
          ·
            refine ⟨393362120765413337079473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262241413843608891386315 393362120765413337079473)
            ·
              refine ⟨295021590574060002809605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393362120765413337079473 295021590574060002809605)
              ·
                refine ⟨55316548232636250526801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295021590574060002809605 55316548232636250526801)
                ·
                  refine ⟨41487411174477187895101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55316548232636250526801 41487411174477187895101)
                  ·
                    refine ⟨15557779190428945460663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41487411174477187895101 15557779190428945460663)
                    ·
                      rfl

theorem cell22_45448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_45448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45448 prefixEnd_45448 := by exact prefixLift 45448
  have htrace : WordTrace (prefixWord ++ tailWord_45448) baseStart_45448 baseEnd_45448 := by
    simpa [prefixWord, tailWord_45448, baseEnd_45448] using wordTrace_append hprefix tailTrace_45448
  have hstable : (prefixWord ++ tailWord_45448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45448).length < 2 ^ (prefixWord ++ tailWord_45448).sum := by decide
  have hdescent : baseEnd_45448 < baseStart_45448 := by decide
  rcases family_descends (prefixWord ++ tailWord_45448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45450 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_45450 : Nat := 118140960795 + 45450 * 2 ^ 59
def prefixEnd_45450 : Nat := 4983230072969 + 3 ^ 40 * 45450 * 2
def baseEnd_45450 : Nat := 5186154610433868970219

theorem tailTrace_45450 : CollatzResearch.WordTrace tailWord_45450 prefixEnd_45450 5186154610433868970219 := by
  unfold tailWord_45450
  simp only [CollatzResearch.WordTrace]
  refine ⟨414424421337471771781451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1105131790233258058083869 414424421337471771781451)
  ·
    refine ⟨621636632006207657672177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414424421337471771781451 621636632006207657672177)
    ·
      refine ⟨466227474004655743254133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 621636632006207657672177 466227474004655743254133)
      ·
        refine ⟨43708825687936475930075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 466227474004655743254133 43708825687936475930075)
        ·
          refine ⟨65563238531904713895113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43708825687936475930075 65563238531904713895113)
          ·
            refine ⟨49172428898928535421335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65563238531904713895113 49172428898928535421335)
            ·
              refine ⟨73758643348392803132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49172428898928535421335 73758643348392803132003)
              ·
                refine ⟨110637965022589204698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73758643348392803132003 110637965022589204698005)
                ·
                  refine ⟨5186154610433868970219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110637965022589204698005 5186154610433868970219)
                  ·
                    rfl

theorem cell22_45450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_45450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45450 prefixEnd_45450 := by exact prefixLift 45450
  have htrace : WordTrace (prefixWord ++ tailWord_45450) baseStart_45450 baseEnd_45450 := by
    simpa [prefixWord, tailWord_45450, baseEnd_45450] using wordTrace_append hprefix tailTrace_45450
  have hstable : (prefixWord ++ tailWord_45450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45450).length < 2 ^ (prefixWord ++ tailWord_45450).sum := by decide
  have hdescent : baseEnd_45450 < baseStart_45450 := by decide
  rcases family_descends (prefixWord ++ tailWord_45450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45480 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_45480 : Nat := 118140960795 + 45480 * 2 ^ 59
def prefixEnd_45480 : Nat := 4983230072969 + 3 ^ 40 * 45480 * 2
def baseEnd_45480 : Nat := 15568733444391528660565

theorem tailTrace_45480 : CollatzResearch.WordTrace tailWord_45480 prefixEnd_45480 15568733444391528660565 := by
  unfold tailWord_45480
  simp only [CollatzResearch.WordTrace]
  refine ⟨829395937620601105358947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1105861250160801473811929 829395937620601105358947)
  ·
    refine ⟨1244093906430901658038421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829395937620601105358947 1244093906430901658038421)
    ·
      refine ⟨58316901863948515220551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1244093906430901658038421 58316901863948515220551)
      ·
        refine ⟨87475352795922772830827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58316901863948515220551 87475352795922772830827)
        ·
          refine ⟨131213029193884159246241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87475352795922772830827 131213029193884159246241)
          ·
            refine ⟨98409771895413119434681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131213029193884159246241 98409771895413119434681)
            ·
              refine ⟨73807328921559839576011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98409771895413119434681 73807328921559839576011)
              ·
                refine ⟨110710993382339759364017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73807328921559839576011 110710993382339759364017)
                ·
                  refine ⟨83033245036754819523013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110710993382339759364017 83033245036754819523013)
                  ·
                    refine ⟨15568733444391528660565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83033245036754819523013 15568733444391528660565)
                    ·
                      rfl

theorem cell22_45480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_45480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45480 prefixEnd_45480 := by exact prefixLift 45480
  have htrace : WordTrace (prefixWord ++ tailWord_45480) baseStart_45480 baseEnd_45480 := by
    simpa [prefixWord, tailWord_45480, baseEnd_45480] using wordTrace_append hprefix tailTrace_45480
  have hstable : (prefixWord ++ tailWord_45480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45480).length < 2 ^ (prefixWord ++ tailWord_45480).sum := by decide
  have hdescent : baseEnd_45480 < baseStart_45480 := by decide
  rcases family_descends (prefixWord ++ tailWord_45480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45482 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_45482 : Nat := 118140960795 + 45482 * 2 ^ 59
def prefixEnd_45482 : Nat := 4983230072969 + 3 ^ 40 * 45482 * 2
def baseEnd_45482 : Nat := 15569418085264190110559

theorem tailTrace_45482 : CollatzResearch.WordTrace tailWord_45482 prefixEnd_45482 15569418085264190110559 := by
  unfold tailWord_45482
  simp only [CollatzResearch.WordTrace]
  refine ⟨414716205308489138072675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1105909880822637701527133 414716205308489138072675)
  ·
    refine ⟨622074307962733707109013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414716205308489138072675 622074307962733707109013)
    ·
      refine ⟨29159733185753142520735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 622074307962733707109013 29159733185753142520735)
      ·
        refine ⟨43739599778629713781103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29159733185753142520735 43739599778629713781103)
        ·
          refine ⟨65609399667944570671655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43739599778629713781103 65609399667944570671655)
          ·
            refine ⟨98414099501916856007483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65609399667944570671655 98414099501916856007483)
            ·
              refine ⟨147621149252875284011225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98414099501916856007483 147621149252875284011225)
              ·
                refine ⟨110715861939656463008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147621149252875284011225 110715861939656463008419)
                ·
                  refine ⟨166073792909484694512629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110715861939656463008419 166073792909484694512629)
                  ·
                    refine ⟨15569418085264190110559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166073792909484694512629 15569418085264190110559)
                    ·
                      rfl

theorem cell22_45482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_45482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45482 prefixEnd_45482 := by exact prefixLift 45482
  have htrace : WordTrace (prefixWord ++ tailWord_45482) baseStart_45482 baseEnd_45482 := by
    simpa [prefixWord, tailWord_45482, baseEnd_45482] using wordTrace_append hprefix tailTrace_45482
  have hstable : (prefixWord ++ tailWord_45482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45482).length < 2 ^ (prefixWord ++ tailWord_45482).sum := by decide
  have hdescent : baseEnd_45482 < baseStart_45482 := by decide
  rcases family_descends (prefixWord ++ tailWord_45482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45536 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_45536 : Nat := 118140960795 + 45536 * 2 ^ 59
def prefixEnd_45536 : Nat := 4983230072969 + 3 ^ 40 * 45536 * 2
def baseEnd_45536 : Nat := 15587903388826049260393

theorem tailTrace_45536 : CollatzResearch.WordTrace tailWord_45536 prefixEnd_45536 15587903388826049260393 := by
  unfold tailWord_45536
  simp only [CollatzResearch.WordTrace]
  refine ⟨830417181519161887378231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1107222908692215849837641 830417181519161887378231)
  ·
    refine ⟨1245625772278742831067347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 830417181519161887378231 1245625772278742831067347)
    ·
      refine ⟨1868438658418114246601021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245625772278742831067347 1868438658418114246601021)
      ·
        refine ⟨700664496906792842475383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1868438658418114246601021 700664496906792842475383)
        ·
          refine ⟨1050996745360189263713075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700664496906792842475383 1050996745360189263713075)
          ·
            refine ⟨1576495118040283895569613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050996745360189263713075 1576495118040283895569613)
            ·
              refine ⟨591185669265106460838605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576495118040283895569613 591185669265106460838605)
              ·
                refine ⟨221694625974414922814477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591185669265106460838605 221694625974414922814477)
                ·
                  refine ⟨83135484740405596055429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221694625974414922814477 83135484740405596055429)
                  ·
                    refine ⟨15587903388826049260393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83135484740405596055429 15587903388826049260393)
                    ·
                      rfl

theorem cell22_45536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_45536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45536 prefixEnd_45536 := by exact prefixLift 45536
  have htrace : WordTrace (prefixWord ++ tailWord_45536) baseStart_45536 baseEnd_45536 := by
    simpa [prefixWord, tailWord_45536, baseEnd_45536] using wordTrace_append hprefix tailTrace_45536
  have hstable : (prefixWord ++ tailWord_45536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45536).length < 2 ^ (prefixWord ++ tailWord_45536).sum := by decide
  have hdescent : baseEnd_45536 < baseStart_45536 := by decide
  rcases family_descends (prefixWord ++ tailWord_45536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45553 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_45553 : Nat := 118140960795 + 45553 * 2 ^ 59
def prefixEnd_45553 : Nat := 4983230072969 + 3 ^ 40 * 45553 * 2
def baseEnd_45553 : Nat := 15593722836243671585341

theorem tailTrace_45553 : CollatzResearch.WordTrace tailWord_45553 prefixEnd_45553 15593722836243671585341 := by
  unfold tailWord_45553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661454403976735678125313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1107636269317823785416875 1661454403976735678125313)
  ·
    refine ⟨1246090802982551758593985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1661454403976735678125313 1246090802982551758593985)
    ·
      refine ⟨934568102236913818945489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246090802982551758593985 934568102236913818945489)
      ·
        refine ⟨700926076677685364209117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 934568102236913818945489 700926076677685364209117)
        ·
          refine ⟨262847278754132011578419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700926076677685364209117 262847278754132011578419)
          ·
            refine ⟨394270918131198017367629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262847278754132011578419 394270918131198017367629)
            ·
              refine ⟨147851594299199256512861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394270918131198017367629 147851594299199256512861)
              ·
                refine ⟨55444347862199721192323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147851594299199256512861 55444347862199721192323)
                ·
                  refine ⟨83166521793299581788485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55444347862199721192323 83166521793299581788485)
                  ·
                    refine ⟨15593722836243671585341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83166521793299581788485 15593722836243671585341)
                    ·
                      rfl

theorem cell22_45553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_45553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45553 prefixEnd_45553 := by exact prefixLift 45553
  have htrace : WordTrace (prefixWord ++ tailWord_45553) baseStart_45553 baseEnd_45553 := by
    simpa [prefixWord, tailWord_45553, baseEnd_45553] using wordTrace_append hprefix tailTrace_45553
  have hstable : (prefixWord ++ tailWord_45553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45553).length < 2 ^ (prefixWord ++ tailWord_45553).sum := by decide
  have hdescent : baseEnd_45553 < baseStart_45553 := by decide
  rcases family_descends (prefixWord ++ tailWord_45553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45557 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 5]
def baseStart_45557 : Nat := 118140960795 + 45557 * 2 ^ 59
def prefixEnd_45557 : Nat := 4983230072969 + 3 ^ 40 * 45557 * 2
def baseEnd_45557 : Nat := 5198364039329664828443

theorem tailTrace_45557 : CollatzResearch.WordTrace tailWord_45557 prefixEnd_45557 5198364039329664828443 := by
  unfold tailWord_45557
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661600295962244361270925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1107733530641496240847283 1661600295962244361270925)
  ·
    refine ⟨623100110985841635476597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1661600295962244361270925 623100110985841635476597)
    ·
      refine ⟨58415635404922653325931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 623100110985841635476597 58415635404922653325931)
      ·
        refine ⟨87623453107383979988897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58415635404922653325931 87623453107383979988897)
        ·
          refine ⟨65717589830537984991673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87623453107383979988897 65717589830537984991673)
          ·
            refine ⟨49288192372903488743755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65717589830537984991673 49288192372903488743755)
            ·
              refine ⟨73932288559355233115633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49288192372903488743755 73932288559355233115633)
              ·
                refine ⟨55449216419516424836725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73932288559355233115633 55449216419516424836725)
                ·
                  refine ⟨5198364039329664828443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55449216419516424836725 5198364039329664828443)
                  ·
                    rfl

theorem cell22_45557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_45557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45557 prefixEnd_45557 := by exact prefixLift 45557
  have htrace : WordTrace (prefixWord ++ tailWord_45557) baseStart_45557 baseEnd_45557 := by
    simpa [prefixWord, tailWord_45557, baseEnd_45557] using wordTrace_append hprefix tailTrace_45557
  have hstable : (prefixWord ++ tailWord_45557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45557).length < 2 ^ (prefixWord ++ tailWord_45557).sum := by decide
  have hdescent : baseEnd_45557 < baseStart_45557 := by decide
  rcases family_descends (prefixWord ++ tailWord_45557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45703 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 6]
def baseStart_45703 : Nat := 118140960795 + 45703 * 2 ^ 59
def prefixEnd_45703 : Nat := 4983230072969 + 3 ^ 40 * 45703 * 2
def baseEnd_45703 : Nat := 5215023633897760111627

theorem tailTrace_45703 : CollatzResearch.WordTrace tailWord_45703 prefixEnd_45703 5215023633897760111627 := by
  unfold tailWord_45703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666925353433311296085763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1111283568955540864057175 1666925353433311296085763)
  ·
    refine ⟨2500388030149966944128645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666925353433311296085763 2500388030149966944128645)
    ·
      refine ⟨468822755653118802024121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2500388030149966944128645 468822755653118802024121)
      ·
        refine ⟨351617066739839101518091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468822755653118802024121 351617066739839101518091)
        ·
          refine ⟨527425600109758652277137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351617066739839101518091 527425600109758652277137)
          ·
            refine ⟨395569200082318989207853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527425600109758652277137 395569200082318989207853)
            ·
              refine ⟨148338450030869620952945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395569200082318989207853 148338450030869620952945)
              ·
                refine ⟨111253837523152215714709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148338450030869620952945 111253837523152215714709)
                ·
                  refine ⟨5215023633897760111627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111253837523152215714709 5215023633897760111627)
                  ·
                    rfl

theorem cell22_45703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_45703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45703 prefixEnd_45703 := by exact prefixLift 45703
  have htrace : WordTrace (prefixWord ++ tailWord_45703) baseStart_45703 baseEnd_45703 := by
    simpa [prefixWord, tailWord_45703, baseEnd_45703] using wordTrace_append hprefix tailTrace_45703
  have hstable : (prefixWord ++ tailWord_45703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45703).length < 2 ^ (prefixWord ++ tailWord_45703).sum := by decide
  have hdescent : baseEnd_45703 < baseStart_45703 := by decide
  rcases family_descends (prefixWord ++ tailWord_45703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45733 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_45733 : Nat := 118140960795 + 45733 * 2 ^ 59
def prefixEnd_45733 : Nat := 4983230072969 + 3 ^ 40 * 45733 * 2
def baseEnd_45733 : Nat := 15655340514783202084789

theorem tailTrace_45733 : CollatzResearch.WordTrace tailWord_45733 prefixEnd_45733 15655340514783202084789 := by
  unfold tailWord_45733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668019543324626419677853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1112013028883084279785235 1668019543324626419677853)
  ·
    refine ⟨625507328746734907379195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1668019543324626419677853 625507328746734907379195)
    ·
      refine ⟨938260993120102361068793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625507328746734907379195 938260993120102361068793)
      ·
        refine ⟨703695744840076770801595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938260993120102361068793 703695744840076770801595)
        ·
          refine ⟨1055543617260115156202393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703695744840076770801595 1055543617260115156202393)
          ·
            refine ⟨791657712945086367151795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055543617260115156202393 791657712945086367151795)
            ·
              refine ⟨1187486569417629550727693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791657712945086367151795 1187486569417629550727693)
              ·
                refine ⟨445307463531611081522885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1187486569417629550727693 445307463531611081522885)
                ·
                  refine ⟨83495149412177077785541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 445307463531611081522885 83495149412177077785541)
                  ·
                    refine ⟨15655340514783202084789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83495149412177077785541 15655340514783202084789)
                    ·
                      rfl

theorem cell22_45733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_45733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45733 prefixEnd_45733 := by exact prefixLift 45733
  have htrace : WordTrace (prefixWord ++ tailWord_45733) baseStart_45733 baseEnd_45733 := by
    simpa [prefixWord, tailWord_45733, baseEnd_45733] using wordTrace_append hprefix tailTrace_45733
  have hstable : (prefixWord ++ tailWord_45733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45733).length < 2 ^ (prefixWord ++ tailWord_45733).sum := by decide
  have hdescent : baseEnd_45733 < baseStart_45733 := by decide
  rcases family_descends (prefixWord ++ tailWord_45733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45797 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_45797 : Nat := 118140960795 + 45797 * 2 ^ 59
def prefixEnd_45797 : Nat := 4983230072969 + 3 ^ 40 * 45797 * 2
def baseEnd_45797 : Nat := 15677249022708368484593

theorem tailTrace_45797 : CollatzResearch.WordTrace tailWord_45797 prefixEnd_45797 15677249022708368484593 := by
  unfold tailWord_45797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670353815092765350007645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1113569210061843566671763 1670353815092765350007645)
  ·
    refine ⟨626382680659787006252867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1670353815092765350007645 626382680659787006252867)
    ·
      refine ⟨939574020989680509379301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626382680659787006252867 939574020989680509379301)
      ·
        refine ⟨176170128935565095508619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 939574020989680509379301 176170128935565095508619)
        ·
          refine ⟨264255193403347643262929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176170128935565095508619 264255193403347643262929)
          ·
            refine ⟨198191395052510732447197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264255193403347643262929 198191395052510732447197)
            ·
              refine ⟨74321773144691524667699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198191395052510732447197 74321773144691524667699)
              ·
                refine ⟨111482659717037287001549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74321773144691524667699 111482659717037287001549)
                ·
                  refine ⟨41805997393888982625581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111482659717037287001549 41805997393888982625581)
                  ·
                    refine ⟨15677249022708368484593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41805997393888982625581 15677249022708368484593)
                    ·
                      rfl

theorem cell22_45797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_45797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45797 prefixEnd_45797 := by exact prefixLift 45797
  have htrace : WordTrace (prefixWord ++ tailWord_45797) baseStart_45797 baseEnd_45797 := by
    simpa [prefixWord, tailWord_45797, baseEnd_45797] using wordTrace_append hprefix tailTrace_45797
  have hstable : (prefixWord ++ tailWord_45797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45797).length < 2 ^ (prefixWord ++ tailWord_45797).sum := by decide
  have hdescent : baseEnd_45797 < baseStart_45797 := by decide
  rcases family_descends (prefixWord ++ tailWord_45797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45808 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_45808 : Nat := 118140960795 + 45808 * 2 ^ 59
def prefixEnd_45808 : Nat := 4983230072969 + 3 ^ 40 * 45808 * 2
def baseEnd_45808 : Nat := 15681014547508006459559

theorem tailTrace_45808 : CollatzResearch.WordTrace tailWord_45808 prefixEnd_45808 15681014547508006459559 := by
  unfold tailWord_45808
  simp only [CollatzResearch.WordTrace]
  refine ⟨835377509026457114329039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1113836678701942819105385 835377509026457114329039)
  ·
    refine ⟨1253066263539685671493559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835377509026457114329039 1253066263539685671493559)
    ·
      refine ⟨1879599395309528507240339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253066263539685671493559 1879599395309528507240339)
      ·
        refine ⟨2819399092964292760860509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879599395309528507240339 2819399092964292760860509)
        ·
          refine ⟨1057274659861609785322691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2819399092964292760860509 1057274659861609785322691)
          ·
            refine ⟨1585911989792414677984037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057274659861609785322691 1585911989792414677984037)
            ·
              refine ⟨297358498086077752122007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1585911989792414677984037 297358498086077752122007)
              ·
                refine ⟨446037747129116628183011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297358498086077752122007 446037747129116628183011)
                ·
                  refine ⟨669056620693674942274517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446037747129116628183011 669056620693674942274517)
                  ·
                    refine ⟨15681014547508006459559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 669056620693674942274517 15681014547508006459559)
                    ·
                      rfl

theorem cell22_45808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_45808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45808 prefixEnd_45808 := by exact prefixLift 45808
  have htrace : WordTrace (prefixWord ++ tailWord_45808) baseStart_45808 baseEnd_45808 := by
    simpa [prefixWord, tailWord_45808, baseEnd_45808] using wordTrace_append hprefix tailTrace_45808
  have hstable : (prefixWord ++ tailWord_45808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45808).length < 2 ^ (prefixWord ++ tailWord_45808).sum := by decide
  have hdescent : baseEnd_45808 < baseStart_45808 := by decide
  rcases family_descends (prefixWord ++ tailWord_45808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45900 : List Nat := [2, 2, 1, 3, 3, 2, 9]
def baseStart_45900 : Nat := 118140960795 + 45900 * 2 ^ 59
def prefixEnd_45900 : Nat := 4983230072969 + 3 ^ 40 * 45900 * 2
def baseEnd_45900 : Nat := 581944741764830857751

theorem tailTrace_45900 : CollatzResearch.WordTrace tailWord_45900 prefixEnd_45900 581944741764830857751 := by
  unfold tailWord_45900
  simp only [CollatzResearch.WordTrace]
  refine ⟨837055266859806970503577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1116073689146409294004769 837055266859806970503577)
  ·
    refine ⟨627791450144855227877683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 837055266859806970503577 627791450144855227877683)
    ·
      refine ⟨941687175217282841816525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627791450144855227877683 941687175217282841816525)
      ·
        refine ⟨353132690706481065681197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 941687175217282841816525 353132690706481065681197)
        ·
          refine ⟨132424759014930399630449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353132690706481065681197 132424759014930399630449)
          ·
            refine ⟨99318569261197799722837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132424759014930399630449 99318569261197799722837)
            ·
              refine ⟨581944741764830857751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 99318569261197799722837 581944741764830857751)
              ·
                rfl

theorem cell22_45900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 9].length) (baseStart_45900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45900 prefixEnd_45900 := by exact prefixLift 45900
  have htrace : WordTrace (prefixWord ++ tailWord_45900) baseStart_45900 baseEnd_45900 := by
    simpa [prefixWord, tailWord_45900, baseEnd_45900] using wordTrace_append hprefix tailTrace_45900
  have hstable : (prefixWord ++ tailWord_45900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45900).length < 2 ^ (prefixWord ++ tailWord_45900).sum := by decide
  have hdescent : baseEnd_45900 < baseStart_45900 := by decide
  rcases family_descends (prefixWord ++ tailWord_45900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45932 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_45932 : Nat := 118140960795 + 45932 * 2 ^ 59
def prefixEnd_45932 : Nat := 4983230072969 + 3 ^ 40 * 45932 * 2
def baseEnd_45932 : Nat := 15723462281613016359179

theorem tailTrace_45932 : CollatzResearch.WordTrace tailWord_45932 prefixEnd_45932 15723462281613016359179 := by
  unfold tailWord_45932
  simp only [CollatzResearch.WordTrace]
  refine ⟨837638834801841703086025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1116851779735788937448033 837638834801841703086025)
  ·
    refine ⟨628229126101381277314519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 837638834801841703086025 628229126101381277314519)
    ·
      refine ⟨942343689152071915971779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628229126101381277314519 942343689152071915971779)
      ·
        refine ⟨1413515533728107873957669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942343689152071915971779 1413515533728107873957669)
        ·
          refine ⟨265034162574020226367063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1413515533728107873957669 265034162574020226367063)
          ·
            refine ⟨397551243861030339550595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265034162574020226367063 397551243861030339550595)
            ·
              refine ⟨596326865791545509325893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397551243861030339550595 596326865791545509325893)
              ·
                refine ⟨111811287335914782998605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596326865791545509325893 111811287335914782998605)
                ·
                  refine ⟨41929232750968043624477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111811287335914782998605 41929232750968043624477)
                  ·
                    refine ⟨15723462281613016359179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41929232750968043624477 15723462281613016359179)
                    ·
                      rfl

theorem cell22_45932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_45932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45932 prefixEnd_45932 := by exact prefixLift 45932
  have htrace : WordTrace (prefixWord ++ tailWord_45932) baseStart_45932 baseEnd_45932 := by
    simpa [prefixWord, tailWord_45932, baseEnd_45932] using wordTrace_append hprefix tailTrace_45932
  have hstable : (prefixWord ++ tailWord_45932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45932).length < 2 ^ (prefixWord ++ tailWord_45932).sum := by decide
  have hdescent : baseEnd_45932 < baseStart_45932 := by decide
  rcases family_descends (prefixWord ++ tailWord_45932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45945 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 7]
def baseStart_45945 : Nat := 118140960795 + 45945 * 2 ^ 59
def prefixEnd_45945 : Nat := 4983230072969 + 3 ^ 40 * 45945 * 2
def baseEnd_45945 : Nat := 5242637482428438594713

theorem tailTrace_45945 : CollatzResearch.WordTrace tailWord_45945 prefixEnd_45945 5242637482428438594713 := by
  unfold tailWord_45945
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675751818556586626395289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1117167879037724417596859 1675751818556586626395289)
  ·
    refine ⟨1256813863917439969796467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675751818556586626395289 1256813863917439969796467)
    ·
      refine ⟨1885220795876159954694701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256813863917439969796467 1885220795876159954694701)
      ·
        refine ⟨706957798453559983010513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1885220795876159954694701 706957798453559983010513)
        ·
          refine ⟨530218348840169987257885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706957798453559983010513 530218348840169987257885)
          ·
            refine ⟨198831880815063745221707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 530218348840169987257885 198831880815063745221707)
            ·
              refine ⟨298247821222595617832561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198831880815063745221707 298247821222595617832561)
              ·
                refine ⟨223685865916946713374421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298247821222595617832561 223685865916946713374421)
                ·
                  refine ⟨5242637482428438594713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223685865916946713374421 5242637482428438594713)
                  ·
                    rfl

theorem cell22_45945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_45945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45945 prefixEnd_45945 := by exact prefixLift 45945
  have htrace : WordTrace (prefixWord ++ tailWord_45945) baseStart_45945 baseEnd_45945 := by
    simpa [prefixWord, tailWord_45945, baseEnd_45945] using wordTrace_append hprefix tailTrace_45945
  have hstable : (prefixWord ++ tailWord_45945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45945).length < 2 ^ (prefixWord ++ tailWord_45945).sum := by decide
  have hdescent : baseEnd_45945 < baseStart_45945 := by decide
  rcases family_descends (prefixWord ++ tailWord_45945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45962 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_45962 : Nat := 118140960795 + 45962 * 2 ^ 59
def prefixEnd_45962 : Nat := 4983230072969 + 3 ^ 40 * 45962 * 2
def baseEnd_45962 : Nat := 5244577298234312703029

theorem tailTrace_45962 : CollatzResearch.WordTrace tailWord_45962 prefixEnd_45962 5244577298234312703029 := by
  unfold tailWord_45962
  simp only [CollatzResearch.WordTrace]
  refine ⟨419092964873749632441035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1117581239663332353176093 419092964873749632441035)
  ·
    refine ⟨628639447310624448661553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419092964873749632441035 628639447310624448661553)
    ·
      refine ⟨471479585482968336496165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628639447310624448661553 471479585482968336496165)
      ·
        refine ⟨88402422278056563093031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471479585482968336496165 88402422278056563093031)
        ·
          refine ⟨132603633417084844639547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88402422278056563093031 132603633417084844639547)
          ·
            refine ⟨198905450125627266959321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132603633417084844639547 198905450125627266959321)
            ·
              refine ⟨149179087594220450219491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198905450125627266959321 149179087594220450219491)
              ·
                refine ⟨223768631391330675329237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149179087594220450219491 223768631391330675329237)
                ·
                  refine ⟨5244577298234312703029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223768631391330675329237 5244577298234312703029)
                  ·
                    rfl

theorem cell22_45962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_45962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_45962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_45962 prefixEnd_45962 := by exact prefixLift 45962
  have htrace : WordTrace (prefixWord ++ tailWord_45962) baseStart_45962 baseEnd_45962 := by
    simpa [prefixWord, tailWord_45962, baseEnd_45962] using wordTrace_append hprefix tailTrace_45962
  have hstable : (prefixWord ++ tailWord_45962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45962).length < 2 ^ (prefixWord ++ tailWord_45962).sum := by decide
  have hdescent : baseEnd_45962 < baseStart_45962 := by decide
  rcases family_descends (prefixWord ++ tailWord_45962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46097 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 5]
def baseStart_46097 : Nat := 118140960795 + 46097 * 2 ^ 59
def prefixEnd_46097 : Nat := 4983230072969 + 3 ^ 40 * 46097 * 2
def baseEnd_46097 : Nat := 5259981717869195327891

theorem tailTrace_46097 : CollatzResearch.WordTrace tailWord_46097 prefixEnd_46097 5259981717869195327891 := by
  unfold tailWord_46097
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681295714005916585928545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1120863809337277723952363 1681295714005916585928545)
  ·
    refine ⟨1260971785504437439446409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1681295714005916585928545 1260971785504437439446409)
    ·
      refine ⟨945728839128328079584807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1260971785504437439446409 945728839128328079584807)
      ·
        refine ⟨1418593258692492119377211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945728839128328079584807 1418593258692492119377211)
        ·
          refine ⟨2127889888038738179065817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418593258692492119377211 2127889888038738179065817)
          ·
            refine ⟨1595917416029053634299363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127889888038738179065817 1595917416029053634299363)
            ·
              refine ⟨2393876124043580451449045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595917416029053634299363 2393876124043580451449045)
              ·
                refine ⟨56106471657271416830837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2393876124043580451449045 56106471657271416830837)
                ·
                  refine ⟨5259981717869195327891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56106471657271416830837 5259981717869195327891)
                  ·
                    rfl

theorem cell22_46097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_46097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46097 prefixEnd_46097 := by exact prefixLift 46097
  have htrace : WordTrace (prefixWord ++ tailWord_46097) baseStart_46097 baseEnd_46097 := by
    simpa [prefixWord, tailWord_46097, baseEnd_46097] using wordTrace_append hprefix tailTrace_46097
  have hstable : (prefixWord ++ tailWord_46097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46097).length < 2 ^ (prefixWord ++ tailWord_46097).sum := by decide
  have hdescent : baseEnd_46097 < baseStart_46097 := by decide
  rcases family_descends (prefixWord ++ tailWord_46097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46191 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 2, 3]
def baseStart_46191 : Nat := 118140960795 + 46191 * 2 ^ 59
def prefixEnd_46191 : Nat := 4983230072969 + 3 ^ 40 * 46191 * 2
def baseEnd_46191 : Nat := 15812123274622674133385

theorem tailTrace_46191 : CollatzResearch.WordTrace tailWord_46191 prefixEnd_46191 15812123274622674133385 := by
  unfold tailWord_46191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684724175665370639850427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123149450443580426566951 1684724175665370639850427)
  ·
    refine ⟨2527086263498055959775641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684724175665370639850427 2527086263498055959775641)
    ·
      refine ⟨1895314697623541969831731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2527086263498055959775641 1895314697623541969831731)
      ·
        refine ⟨2842972046435312954747597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895314697623541969831731 2842972046435312954747597)
        ·
          refine ⟨1066114517413242358030349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2842972046435312954747597 1066114517413242358030349)
          ·
            refine ⟨399792944029965884261381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1066114517413242358030349 399792944029965884261381)
            ·
              refine ⟨74961177005618603299009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399792944029965884261381 74961177005618603299009)
              ·
                refine ⟨56220882754213952474257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74961177005618603299009 56220882754213952474257)
                ·
                  refine ⟨42165662065660464355693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56220882754213952474257 42165662065660464355693)
                  ·
                    refine ⟨15812123274622674133385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42165662065660464355693 15812123274622674133385)
                    ·
                      rfl

theorem cell22_46191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_46191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46191 prefixEnd_46191 := by exact prefixLift 46191
  have htrace : WordTrace (prefixWord ++ tailWord_46191) baseStart_46191 baseEnd_46191 := by
    simpa [prefixWord, tailWord_46191, baseEnd_46191] using wordTrace_append hprefix tailTrace_46191
  have hstable : (prefixWord ++ tailWord_46191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46191).length < 2 ^ (prefixWord ++ tailWord_46191).sum := by decide
  have hdescent : baseEnd_46191 < baseStart_46191 := by decide
  rcases family_descends (prefixWord ++ tailWord_46191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46242 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_46242 : Nat := 118140960795 + 46242 * 2 ^ 59
def prefixEnd_46242 : Nat := 4983230072969 + 3 ^ 40 * 46242 * 2
def baseEnd_46242 : Nat := 15829581616875541108229

theorem tailTrace_46242 : CollatzResearch.WordTrace tailWord_46242 prefixEnd_46242 15829581616875541108229 := by
  unfold tailWord_46242
  simp only [CollatzResearch.WordTrace]
  refine ⟨421646074620151587489245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1124389532320404233304653 421646074620151587489245)
  ·
    refine ⟨158117277982556845308467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 421646074620151587489245 158117277982556845308467)
    ·
      refine ⟨237175916973835267962701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158117277982556845308467 237175916973835267962701)
      ·
        refine ⟨88940968865188225486013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237175916973835267962701 88940968865188225486013)
        ·
          refine ⟨33352863324445584557255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88940968865188225486013 33352863324445584557255)
          ·
            refine ⟨50029294986668376835883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33352863324445584557255 50029294986668376835883)
            ·
              refine ⟨75043942480002565253825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50029294986668376835883 75043942480002565253825)
              ·
                refine ⟨56282956860001923940369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75043942480002565253825 56282956860001923940369)
                ·
                  refine ⟨42212217645001442955277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56282956860001923940369 42212217645001442955277)
                  ·
                    refine ⟨15829581616875541108229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42212217645001442955277 15829581616875541108229)
                    ·
                      rfl

theorem cell22_46242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_46242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46242 prefixEnd_46242 := by exact prefixLift 46242
  have htrace : WordTrace (prefixWord ++ tailWord_46242) baseStart_46242 baseEnd_46242 := by
    simpa [prefixWord, tailWord_46242, baseEnd_46242] using wordTrace_append hprefix tailTrace_46242
  have hstable : (prefixWord ++ tailWord_46242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46242).length < 2 ^ (prefixWord ++ tailWord_46242).sum := by decide
  have hdescent : baseEnd_46242 < baseStart_46242 := by decide
  rcases family_descends (prefixWord ++ tailWord_46242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46279 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_46279 : Nat := 118140960795 + 46279 * 2 ^ 59
def prefixEnd_46279 : Nat := 4983230072969 + 3 ^ 40 * 46279 * 2
def baseEnd_46279 : Nat := 15842247473019777933115

theorem tailTrace_46279 : CollatzResearch.WordTrace tailWord_46279 prefixEnd_46279 15842247473019777933115 := by
  unfold tailWord_46279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687933799346561669053891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1125289199564374446035927 1687933799346561669053891)
  ·
    refine ⟨2531900699019842503580837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687933799346561669053891 2531900699019842503580837)
    ·
      refine ⟨474731381066220469421407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2531900699019842503580837 474731381066220469421407)
      ·
        refine ⟨712097071599330704132111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474731381066220469421407 712097071599330704132111)
        ·
          refine ⟨1068145607398996056198167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712097071599330704132111 1068145607398996056198167)
          ·
            refine ⟨1602218411098494084297251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068145607398996056198167 1602218411098494084297251)
            ·
              refine ⟨2403327616647741126445877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602218411098494084297251 2403327616647741126445877)
              ·
                refine ⟨225311964060725730604301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2403327616647741126445877 225311964060725730604301)
                ·
                  refine ⟨84491986522772148976613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225311964060725730604301 84491986522772148976613)
                  ·
                    refine ⟨15842247473019777933115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84491986522772148976613 15842247473019777933115)
                    ·
                      rfl

theorem cell22_46279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_46279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46279 prefixEnd_46279 := by exact prefixLift 46279
  have htrace : WordTrace (prefixWord ++ tailWord_46279) baseStart_46279 baseEnd_46279 := by
    simpa [prefixWord, tailWord_46279, baseEnd_46279] using wordTrace_append hprefix tailTrace_46279
  have hstable : (prefixWord ++ tailWord_46279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46279).length < 2 ^ (prefixWord ++ tailWord_46279).sum := by decide
  have hdescent : baseEnd_46279 < baseStart_46279 := by decide
  rcases family_descends (prefixWord ++ tailWord_46279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46326 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_46326 : Nat := 118140960795 + 46326 * 2 ^ 59
def prefixEnd_46326 : Nat := 4983230072969 + 3 ^ 40 * 46326 * 2
def baseEnd_46326 : Nat := 15858336533527322007971

theorem tailTrace_46326 : CollatzResearch.WordTrace tailWord_46326 prefixEnd_46326 15858336533527322007971 := by
  unfold tailWord_46326
  simp only [CollatzResearch.WordTrace]
  refine ⟨105603001886018043500927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1126432020117525797343221 105603001886018043500927)
  ·
    refine ⟨158404502829027065251391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105603001886018043500927 158404502829027065251391)
    ·
      refine ⟨237606754243540597877087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158404502829027065251391 237606754243540597877087)
      ·
        refine ⟨356410131365310896815631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237606754243540597877087 356410131365310896815631)
        ·
          refine ⟨534615197047966345223447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356410131365310896815631 534615197047966345223447)
          ·
            refine ⟨801922795571949517835171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534615197047966345223447 801922795571949517835171)
            ·
              refine ⟨1202884193357924276752757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801922795571949517835171 1202884193357924276752757)
              ·
                refine ⟨112770393127305400945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202884193357924276752757 112770393127305400945571)
                ·
                  refine ⟨169155589690958101418357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112770393127305400945571 169155589690958101418357)
                  ·
                    refine ⟨15858336533527322007971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169155589690958101418357 15858336533527322007971)
                    ·
                      rfl

theorem cell22_46326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_46326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46326 prefixEnd_46326 := by exact prefixLift 46326
  have htrace : WordTrace (prefixWord ++ tailWord_46326) baseStart_46326 baseEnd_46326 := by
    simpa [prefixWord, tailWord_46326, baseEnd_46326] using wordTrace_append hprefix tailTrace_46326
  have hstable : (prefixWord ++ tailWord_46326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46326).length < 2 ^ (prefixWord ++ tailWord_46326).sum := by decide
  have hdescent : baseEnd_46326 < baseStart_46326 := by decide
  rcases family_descends (prefixWord ++ tailWord_46326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46339 : List Nat := [1, 1, 1, 3, 2, 4, 2, 8]
def baseStart_46339 : Nat := 118140960795 + 46339 * 2 ^ 59
def prefixEnd_46339 : Nat := 4983230072969 + 3 ^ 40 * 46339 * 2
def baseEnd_46339 : Nat := 1762531855466624603659

theorem tailTrace_46339 : CollatzResearch.WordTrace tailWord_46339 prefixEnd_46339 1762531855466624603659 := by
  unfold tailWord_46339
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690122179129191916238071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126748119419461277492047 1690122179129191916238071)
  ·
    refine ⟨2535183268693787874357107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690122179129191916238071 2535183268693787874357107)
    ·
      refine ⟨3802774903040681811535661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535183268693787874357107 3802774903040681811535661)
      ·
        refine ⟨1426040588640255679325873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3802774903040681811535661 1426040588640255679325873)
        ·
          refine ⟨1069530441480191759494405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426040588640255679325873 1069530441480191759494405)
          ·
            refine ⟨200536957777535954905201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1069530441480191759494405 200536957777535954905201)
            ·
              refine ⟨150402718333151966178901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200536957777535954905201 150402718333151966178901)
              ·
                refine ⟨1762531855466624603659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 150402718333151966178901 1762531855466624603659)
                ·
                  rfl

theorem cell22_46339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_46339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46339 prefixEnd_46339 := by exact prefixLift 46339
  have htrace : WordTrace (prefixWord ++ tailWord_46339) baseStart_46339 baseEnd_46339 := by
    simpa [prefixWord, tailWord_46339, baseEnd_46339] using wordTrace_append hprefix tailTrace_46339
  have hstable : (prefixWord ++ tailWord_46339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46339).length < 2 ^ (prefixWord ++ tailWord_46339).sum := by decide
  have hdescent : baseEnd_46339 < baseStart_46339 := by decide
  rcases family_descends (prefixWord ++ tailWord_46339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46341 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_46341 : Nat := 118140960795 + 46341 * 2 ^ 59
def prefixEnd_46341 : Nat := 4983230072969 + 3 ^ 40 * 46341 * 2
def baseEnd_46341 : Nat := 15863471340072282882925

theorem tailTrace_46341 : CollatzResearch.WordTrace tailWord_46341 prefixEnd_46341 15863471340072282882925 := by
  unfold tailWord_46341
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690195125121946257810877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126796750081297505207251 1690195125121946257810877)
  ·
    refine ⟨633823171920729846679079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1690195125121946257810877 633823171920729846679079)
    ·
      refine ⟨950734757881094770018619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633823171920729846679079 950734757881094770018619)
      ·
        refine ⟨1426102136821642155027929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950734757881094770018619 1426102136821642155027929)
        ·
          refine ⟨1069576602616231616270947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426102136821642155027929 1069576602616231616270947)
          ·
            refine ⟨1604364903924347424406421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069576602616231616270947 1604364903924347424406421)
            ·
              refine ⟨75204604871453785519051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1604364903924347424406421 75204604871453785519051)
              ·
                refine ⟨112806907307180678278577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75204604871453785519051 112806907307180678278577)
                ·
                  refine ⟨84605180480385508708933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112806907307180678278577 84605180480385508708933)
                  ·
                    refine ⟨15863471340072282882925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84605180480385508708933 15863471340072282882925)
                    ·
                      rfl

theorem cell22_46341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_46341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46341 prefixEnd_46341 := by exact prefixLift 46341
  have htrace : WordTrace (prefixWord ++ tailWord_46341) baseStart_46341 baseEnd_46341 := by
    simpa [prefixWord, tailWord_46341, baseEnd_46341] using wordTrace_append hprefix tailTrace_46341
  have hstable : (prefixWord ++ tailWord_46341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46341).length < 2 ^ (prefixWord ++ tailWord_46341).sum := by decide
  have hdescent : baseEnd_46341 < baseStart_46341 := by decide
  rcases family_descends (prefixWord ++ tailWord_46341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46448 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_46448 : Nat := 118140960795 + 46448 * 2 ^ 59
def prefixEnd_46448 : Nat := 4983230072969 + 3 ^ 40 * 46448 * 2
def baseEnd_46448 : Nat := 15900099626759670457597

theorem tailTrace_46448 : CollatzResearch.WordTrace tailWord_46448 prefixEnd_46448 15900099626759670457597 := by
  unfold tailWord_46448
  simp only [CollatzResearch.WordTrace]
  refine ⟨847048867867151765977999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1129398490489535687970665 847048867867151765977999)
  ·
    refine ⟨1270573301800727648966999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847048867867151765977999 1270573301800727648966999)
    ·
      refine ⟨1905859952701091473450499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270573301800727648966999 1905859952701091473450499)
      ·
        refine ⟨2858789929051637210175749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905859952701091473450499 2858789929051637210175749)
        ·
          refine ⟨536023111697181976907953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2858789929051637210175749 536023111697181976907953)
          ·
            refine ⟨402017333772886482680965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536023111697181976907953 402017333772886482680965)
            ·
              refine ⟨75378250082416215502681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 402017333772886482680965 75378250082416215502681)
              ·
                refine ⟨56533687561812161627011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75378250082416215502681 56533687561812161627011)
                ·
                  refine ⟨84800531342718242440517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56533687561812161627011 84800531342718242440517)
                  ·
                    refine ⟨15900099626759670457597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84800531342718242440517 15900099626759670457597)
                    ·
                      rfl

theorem cell22_46448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_46448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46448 prefixEnd_46448 := by exact prefixLift 46448
  have htrace : WordTrace (prefixWord ++ tailWord_46448) baseStart_46448 baseEnd_46448 := by
    simpa [prefixWord, tailWord_46448, baseEnd_46448] using wordTrace_append hprefix tailTrace_46448
  have hstable : (prefixWord ++ tailWord_46448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46448).length < 2 ^ (prefixWord ++ tailWord_46448).sum := by decide
  have hdescent : baseEnd_46448 < baseStart_46448 := by decide
  rcases family_descends (prefixWord ++ tailWord_46448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46461 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_46461 : Nat := 118140960795 + 46461 * 2 ^ 59
def prefixEnd_46461 : Nat := 4983230072969 + 3 ^ 40 * 46461 * 2
def baseEnd_46461 : Nat := 15904549792431969882557

theorem tailTrace_46461 : CollatzResearch.WordTrace tailWord_46461 prefixEnd_46461 15904549792431969882557 := by
  unfold tailWord_46461
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694571884687206752179237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1129714589791471168119491 1694571884687206752179237)
  ·
    refine ⟨317732228378851266033607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1694571884687206752179237 317732228378851266033607)
    ·
      refine ⟨476598342568276899050411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317732228378851266033607 476598342568276899050411)
      ·
        refine ⟨714897513852415348575617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476598342568276899050411 714897513852415348575617)
        ·
          refine ⟨536173135389311511431713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714897513852415348575617 536173135389311511431713)
          ·
            refine ⟨402129851541983633573785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536173135389311511431713 402129851541983633573785)
            ·
              refine ⟨301597388656487725180339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402129851541983633573785 301597388656487725180339)
              ·
                refine ⟨452396082984731587770509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301597388656487725180339 452396082984731587770509)
                ·
                  refine ⟨169648531119274345413941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452396082984731587770509 169648531119274345413941)
                  ·
                    refine ⟨15904549792431969882557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169648531119274345413941 15904549792431969882557)
                    ·
                      rfl

theorem cell22_46461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_46461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46461 prefixEnd_46461 := by exact prefixLift 46461
  have htrace : WordTrace (prefixWord ++ tailWord_46461) baseStart_46461 baseEnd_46461 := by
    simpa [prefixWord, tailWord_46461, baseEnd_46461] using wordTrace_append hprefix tailTrace_46461
  have hstable : (prefixWord ++ tailWord_46461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46461).length < 2 ^ (prefixWord ++ tailWord_46461).sum := by decide
  have hdescent : baseEnd_46461 < baseStart_46461 := by decide
  rcases family_descends (prefixWord ++ tailWord_46461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46495 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 2, 3]
def baseStart_46495 : Nat := 118140960795 + 46495 * 2 ^ 59
def prefixEnd_46495 : Nat := 4983230072969 + 3 ^ 40 * 46495 * 2
def baseEnd_46495 : Nat := 15916188687267214532453

theorem tailTrace_46495 : CollatzResearch.WordTrace tailWord_46495 prefixEnd_46495 15916188687267214532453 := by
  unfold tailWord_46495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695811966564030558916939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1130541311042687039277959 1695811966564030558916939)
  ·
    refine ⟨2543717949846045838375409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695811966564030558916939 2543717949846045838375409)
    ·
      refine ⟨1907788462384534378781557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543717949846045838375409 1907788462384534378781557)
      ·
        refine ⟨178855168348550098010771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1907788462384534378781557 178855168348550098010771)
        ·
          refine ⟨268282752522825147016157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178855168348550098010771 268282752522825147016157)
          ·
            refine ⟨100606032196059430131059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268282752522825147016157 100606032196059430131059)
            ·
              refine ⟨150909048294089145196589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100606032196059430131059 150909048294089145196589)
              ·
                refine ⟨56590893110283429448721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150909048294089145196589 56590893110283429448721)
                ·
                  refine ⟨42443169832712572086541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56590893110283429448721 42443169832712572086541)
                  ·
                    refine ⟨15916188687267214532453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42443169832712572086541 15916188687267214532453)
                    ·
                      rfl

theorem cell22_46495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_46495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46495 prefixEnd_46495 := by exact prefixLift 46495
  have htrace : WordTrace (prefixWord ++ tailWord_46495) baseStart_46495 baseEnd_46495 := by
    simpa [prefixWord, tailWord_46495, baseEnd_46495] using wordTrace_append hprefix tailTrace_46495
  have hstable : (prefixWord ++ tailWord_46495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46495).length < 2 ^ (prefixWord ++ tailWord_46495).sum := by decide
  have hdescent : baseEnd_46495 < baseStart_46495 := by decide
  rcases family_descends (prefixWord ++ tailWord_46495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46553 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 5]
def baseStart_46553 : Nat := 118140960795 + 46553 * 2 ^ 59
def prefixEnd_46553 : Nat := 4983230072969 + 3 ^ 40 * 46553 * 2
def baseEnd_46553 : Nat := 5312014424191465527425

theorem tailTrace_46553 : CollatzResearch.WordTrace tailWord_46553 prefixEnd_46553 5312014424191465527425 := by
  unfold tailWord_46553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697927400353906464528313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1131951600235937643018875 1697927400353906464528313)
  ·
    refine ⟨1273445550265429848396235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1697927400353906464528313 1273445550265429848396235)
    ·
      refine ⟨1910168325398144772594353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273445550265429848396235 1910168325398144772594353)
      ·
        refine ⟨1432626244048608579445765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910168325398144772594353 1432626244048608579445765)
        ·
          refine ⟨268617420759114108646081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1432626244048608579445765 268617420759114108646081)
          ·
            refine ⟨201463065569335581484561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268617420759114108646081 201463065569335581484561)
            ·
              refine ⟨151097299177001686113421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201463065569335581484561 151097299177001686113421)
              ·
                refine ⟨56661487191375632292533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151097299177001686113421 56661487191375632292533)
                ·
                  refine ⟨5312014424191465527425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56661487191375632292533 5312014424191465527425)
                  ·
                    rfl

theorem cell22_46553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_46553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46553 prefixEnd_46553 := by exact prefixLift 46553
  have htrace : WordTrace (prefixWord ++ tailWord_46553) baseStart_46553 baseEnd_46553 := by
    simpa [prefixWord, tailWord_46553, baseEnd_46553] using wordTrace_append hprefix tailTrace_46553
  have hstable : (prefixWord ++ tailWord_46553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46553).length < 2 ^ (prefixWord ++ tailWord_46553).sum := by decide
  have hdescent : baseEnd_46553 < baseStart_46553 := by decide
  rcases family_descends (prefixWord ++ tailWord_46553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46643 : List Nat := [1, 1, 1, 2, 4, 5, 8]
def baseStart_46643 : Nat := 118140960795 + 46643 * 2 ^ 59
def prefixEnd_46643 : Nat := 4983230072969 + 3 ^ 40 * 46643 * 2
def baseEnd_46643 : Nat := 591364893031265253037

theorem tailTrace_46643 : CollatzResearch.WordTrace tailWord_46643 prefixEnd_46643 591364893031265253037 := by
  unfold tailWord_46643
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701209970027851835304583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1134139980018567890203055 1701209970027851835304583)
  ·
    refine ⟨2551814955041777752956875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701209970027851835304583 2551814955041777752956875)
    ·
      refine ⟨3827722432562666629435313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551814955041777752956875 3827722432562666629435313)
      ·
        refine ⟨2870791824421999972076485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3827722432562666629435313 2870791824421999972076485)
        ·
          refine ⟨538273467079124994764341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2870791824421999972076485 538273467079124994764341)
          ·
            refine ⟨50463137538667968259157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 538273467079124994764341 50463137538667968259157)
            ·
              refine ⟨591364893031265253037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 50463137538667968259157 591364893031265253037)
              ·
                rfl

theorem cell22_46643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 8].length) (baseStart_46643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46643 prefixEnd_46643 := by exact prefixLift 46643
  have htrace : WordTrace (prefixWord ++ tailWord_46643) baseStart_46643 baseEnd_46643 := by
    simpa [prefixWord, tailWord_46643, baseEnd_46643] using wordTrace_append hprefix tailTrace_46643
  have hstable : (prefixWord ++ tailWord_46643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46643).length < 2 ^ (prefixWord ++ tailWord_46643).sum := by decide
  have hdescent : baseEnd_46643 < baseStart_46643 := by decide
  rcases family_descends (prefixWord ++ tailWord_46643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46645 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_46645 : Nat := 118140960795 + 46645 * 2 ^ 59
def prefixEnd_46645 : Nat := 4983230072969 + 3 ^ 40 * 46645 * 2
def baseEnd_46645 : Nat := 15967536752716823281993

theorem tailTrace_46645 : CollatzResearch.WordTrace tailWord_46645 prefixEnd_46645 15967536752716823281993 := by
  unfold tailWord_46645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701282916020606176877389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1134188610680404117918259 1701282916020606176877389)
  ·
    refine ⟨637981093507727316329021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1701282916020606176877389 637981093507727316329021)
    ·
      refine ⟨239242910065397743623383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 637981093507727316329021 239242910065397743623383)
      ·
        refine ⟨358864365098096615435075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239242910065397743623383 358864365098096615435075)
        ·
          refine ⟨538296547647144923152613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358864365098096615435075 538296547647144923152613)
          ·
            refine ⟨100930602683839673091115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538296547647144923152613 100930602683839673091115)
            ·
              refine ⟨151395904025759509636673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100930602683839673091115 151395904025759509636673)
              ·
                refine ⟨113546928019319632227505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151395904025759509636673 113546928019319632227505)
                ·
                  refine ⟨85160196014489724170629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113546928019319632227505 85160196014489724170629)
                  ·
                    refine ⟨15967536752716823281993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85160196014489724170629 15967536752716823281993)
                    ·
                      rfl

theorem cell22_46645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_46645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46645 prefixEnd_46645 := by exact prefixLift 46645
  have htrace : WordTrace (prefixWord ++ tailWord_46645) baseStart_46645 baseEnd_46645 := by
    simpa [prefixWord, tailWord_46645, baseEnd_46645] using wordTrace_append hprefix tailTrace_46645
  have hstable : (prefixWord ++ tailWord_46645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46645).length < 2 ^ (prefixWord ++ tailWord_46645).sum := by decide
  have hdescent : baseEnd_46645 < baseStart_46645 := by decide
  rcases family_descends (prefixWord ++ tailWord_46645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46703 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_46703 : Nat := 118140960795 + 46703 * 2 ^ 59
def prefixEnd_46703 : Nat := 4983230072969 + 3 ^ 40 * 46703 * 2
def baseEnd_46703 : Nat := 15987391338024005331815

theorem tailTrace_46703 : CollatzResearch.WordTrace tailWord_46703 prefixEnd_46703 15987391338024005331815 := by
  unfold tailWord_46703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703398349810482082488763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135598899873654721659175 1703398349810482082488763)
  ·
    refine ⟨2555097524715723123733145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1703398349810482082488763 2555097524715723123733145)
    ·
      refine ⟨1916323143536792342799859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2555097524715723123733145 1916323143536792342799859)
      ·
        refine ⟨2874484715305188514199789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916323143536792342799859 2874484715305188514199789)
        ·
          refine ⟨1077931768239445692824921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2874484715305188514199789 1077931768239445692824921)
          ·
            refine ⟨808448826179584269618691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077931768239445692824921 808448826179584269618691)
            ·
              refine ⟨1212673239269376404428037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808448826179584269618691 1212673239269376404428037)
              ·
                refine ⟨227376232363008075830257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1212673239269376404428037 227376232363008075830257)
                ·
                  refine ⟨170532174272256056872693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227376232363008075830257 170532174272256056872693)
                  ·
                    refine ⟨15987391338024005331815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170532174272256056872693 15987391338024005331815)
                    ·
                      rfl

theorem cell22_46703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_46703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46703 prefixEnd_46703 := by exact prefixLift 46703
  have htrace : WordTrace (prefixWord ++ tailWord_46703) baseStart_46703 baseEnd_46703 := by
    simpa [prefixWord, tailWord_46703, baseEnd_46703] using wordTrace_append hprefix tailTrace_46703
  have hstable : (prefixWord ++ tailWord_46703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46703).length < 2 ^ (prefixWord ++ tailWord_46703).sum := by decide
  have hdescent : baseEnd_46703 < baseStart_46703 := by decide
  rcases family_descends (prefixWord ++ tailWord_46703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46752 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_46752 : Nat := 118140960795 + 46752 * 2 ^ 59
def prefixEnd_46752 : Nat := 4983230072969 + 3 ^ 40 * 46752 * 2
def baseEnd_46752 : Nat := 16004165039404210856665

theorem tailTrace_46752 : CollatzResearch.WordTrace tailWord_46752 prefixEnd_46752 16004165039404210856665 := by
  unfold tailWord_46752
  simp only [CollatzResearch.WordTrace]
  refine ⟨852592763316481725511255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1136790351088642300681673 852592763316481725511255)
  ·
    refine ⟨1278889144974722588266883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852592763316481725511255 1278889144974722588266883)
    ·
      refine ⟨1918333717462083882400325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278889144974722588266883 1918333717462083882400325)
      ·
        refine ⟨359687572024140727950061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1918333717462083882400325 359687572024140727950061)
        ·
          refine ⟨134882839509052772981273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359687572024140727950061 134882839509052772981273)
          ·
            refine ⟨101162129631789579735955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134882839509052772981273 101162129631789579735955)
            ·
              refine ⟨151743194447684369603933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101162129631789579735955 151743194447684369603933)
              ·
                refine ⟨56903697917881638601475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151743194447684369603933 56903697917881638601475)
                ·
                  refine ⟨85355546876822457902213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56903697917881638601475 85355546876822457902213)
                  ·
                    refine ⟨16004165039404210856665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85355546876822457902213 16004165039404210856665)
                    ·
                      rfl

theorem cell22_46752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_46752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46752 prefixEnd_46752 := by exact prefixLift 46752
  have htrace : WordTrace (prefixWord ++ tailWord_46752) baseStart_46752 baseEnd_46752 := by
    simpa [prefixWord, tailWord_46752, baseEnd_46752] using wordTrace_append hprefix tailTrace_46752
  have hstable : (prefixWord ++ tailWord_46752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46752).length < 2 ^ (prefixWord ++ tailWord_46752).sum := by decide
  have hdescent : baseEnd_46752 < baseStart_46752 := by decide
  rcases family_descends (prefixWord ++ tailWord_46752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46780 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_46780 : Nat := 118140960795 + 46780 * 2 ^ 59
def prefixEnd_46780 : Nat := 4983230072969 + 3 ^ 40 * 46780 * 2
def baseEnd_46780 : Nat := 16013750011621471156579

theorem tailTrace_46780 : CollatzResearch.WordTrace tailWord_46780 prefixEnd_46780 16013750011621471156579 := by
  unfold tailWord_46780
  simp only [CollatzResearch.WordTrace]
  refine ⟨853103385265762116520897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1137471180354349488694529 853103385265762116520897)
  ·
    refine ⟨639827538949321587390673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 853103385265762116520897 639827538949321587390673)
    ·
      refine ⟨479870654211991190543005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 639827538949321587390673 479870654211991190543005)
      ·
        refine ⟨179951495329496696453627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 479870654211991190543005 179951495329496696453627)
        ·
          refine ⟨269927242994245044680441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179951495329496696453627 269927242994245044680441)
          ·
            refine ⟨202445432245683783510331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269927242994245044680441 202445432245683783510331)
            ·
              refine ⟨303668148368525675265497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202445432245683783510331 303668148368525675265497)
              ·
                refine ⟨227751111276394256449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303668148368525675265497 227751111276394256449123)
                ·
                  refine ⟨341626666914591384673685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227751111276394256449123 341626666914591384673685)
                  ·
                    refine ⟨16013750011621471156579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 341626666914591384673685 16013750011621471156579)
                    ·
                      rfl

theorem cell22_46780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_46780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46780 prefixEnd_46780 := by exact prefixLift 46780
  have htrace : WordTrace (prefixWord ++ tailWord_46780) baseStart_46780 baseEnd_46780 := by
    simpa [prefixWord, tailWord_46780, baseEnd_46780] using wordTrace_append hprefix tailTrace_46780
  have hstable : (prefixWord ++ tailWord_46780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46780).length < 2 ^ (prefixWord ++ tailWord_46780).sum := by decide
  have hdescent : baseEnd_46780 < baseStart_46780 := by decide
  rcases family_descends (prefixWord ++ tailWord_46780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46782 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_46782 : Nat := 118140960795 + 46782 * 2 ^ 59
def prefixEnd_46782 : Nat := 4983230072969 + 3 ^ 40 * 46782 * 2
def baseEnd_46782 : Nat := 16014434652494132606573

theorem tailTrace_46782 : CollatzResearch.WordTrace tailWord_46782 prefixEnd_46782 16014434652494132606573 := by
  unfold tailWord_46782
  simp only [CollatzResearch.WordTrace]
  refine ⟨213284964565534821826825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1137519811016185716409733 213284964565534821826825)
  ·
    refine ⟨159963723424151116370119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213284964565534821826825 159963723424151116370119)
    ·
      refine ⟨239945585136226674555179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159963723424151116370119 239945585136226674555179)
      ·
        refine ⟨359918377704340011832769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239945585136226674555179 359918377704340011832769)
        ·
          refine ⟨269938783278255008874577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359918377704340011832769 269938783278255008874577)
          ·
            refine ⟨202454087458691256655933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269938783278255008874577 202454087458691256655933)
            ·
              refine ⟨75920282797009221245975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202454087458691256655933 75920282797009221245975)
              ·
                refine ⟨113880424195513831868963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75920282797009221245975 113880424195513831868963)
                ·
                  refine ⟨170820636293270747803445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113880424195513831868963 170820636293270747803445)
                  ·
                    refine ⟨16014434652494132606573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 170820636293270747803445 16014434652494132606573)
                    ·
                      rfl

theorem cell22_46782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_46782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46782 prefixEnd_46782 := by exact prefixLift 46782
  have htrace : WordTrace (prefixWord ++ tailWord_46782) baseStart_46782 baseEnd_46782 := by
    simpa [prefixWord, tailWord_46782, baseEnd_46782] using wordTrace_append hprefix tailTrace_46782
  have hstable : (prefixWord ++ tailWord_46782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46782).length < 2 ^ (prefixWord ++ tailWord_46782).sum := by decide
  have hdescent : baseEnd_46782 < baseStart_46782 := by decide
  rcases family_descends (prefixWord ++ tailWord_46782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46827 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 3, 3]
def baseStart_46827 : Nat := 118140960795 + 46827 * 2 ^ 59
def prefixEnd_46827 : Nat := 4983230072969 + 3 ^ 40 * 46827 * 2
def baseEnd_46827 : Nat := 16029839072129015231435

theorem tailTrace_46827 : CollatzResearch.WordTrace tailWord_46827 prefixEnd_46827 16029839072129015231435 := by
  unfold tailWord_46827
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707921001361251260002735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1138614000907500840001823 1707921001361251260002735)
  ·
    refine ⟨2561881502041876890004103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1707921001361251260002735 2561881502041876890004103)
    ·
      refine ⟨3842822253062815335006155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561881502041876890004103 3842822253062815335006155)
      ·
        refine ⟨5764233379594223002509233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3842822253062815335006155 5764233379594223002509233)
        ·
          refine ⟨4323175034695667251881925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764233379594223002509233 4323175034695667251881925)
          ·
            refine ⟨810595319005437609727861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4323175034695667251881925 810595319005437609727861)
            ·
              refine ⟨75993311156759775911987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 810595319005437609727861 75993311156759775911987)
              ·
                refine ⟨113989966735139663867981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75993311156759775911987 113989966735139663867981)
                ·
                  refine ⟨42746237525677373950493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113989966735139663867981 42746237525677373950493)
                  ·
                    refine ⟨16029839072129015231435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42746237525677373950493 16029839072129015231435)
                    ·
                      rfl

theorem cell22_46827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 3].length) (baseStart_46827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46827 prefixEnd_46827 := by exact prefixLift 46827
  have htrace : WordTrace (prefixWord ++ tailWord_46827) baseStart_46827 baseEnd_46827 := by
    simpa [prefixWord, tailWord_46827, baseEnd_46827] using wordTrace_append hprefix tailTrace_46827
  have hstable : (prefixWord ++ tailWord_46827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46827).length < 2 ^ (prefixWord ++ tailWord_46827).sum := by decide
  have hdescent : baseEnd_46827 < baseStart_46827 := by decide
  rcases family_descends (prefixWord ++ tailWord_46827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46917 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_46917 : Nat := 118140960795 + 46917 * 2 ^ 59
def prefixEnd_46917 : Nat := 4983230072969 + 3 ^ 40 * 46917 * 2
def baseEnd_46917 : Nat := 16060647911398780481159

theorem tailTrace_46917 : CollatzResearch.WordTrace tailWord_46917 prefixEnd_46917 16060647911398780481159 := by
  unfold tailWord_46917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711203571035196630779005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1140802380690131087186003 1711203571035196630779005)
  ·
    refine ⟨641701339138198736542127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1711203571035196630779005 641701339138198736542127)
    ·
      refine ⟨962552008707298104813191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 641701339138198736542127 962552008707298104813191)
      ·
        refine ⟨1443828013060947157219787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962552008707298104813191 1443828013060947157219787)
        ·
          refine ⟨2165742019591420735829681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443828013060947157219787 2165742019591420735829681)
          ·
            refine ⟨1624306514693565551872261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2165742019591420735829681 1624306514693565551872261)
            ·
              refine ⟨304557471505043540976049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1624306514693565551872261 304557471505043540976049)
              ·
                refine ⟨228418103628782655732037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304557471505043540976049 228418103628782655732037)
                ·
                  refine ⟨42828394430396747949757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228418103628782655732037 42828394430396747949757)
                  ·
                    refine ⟨16060647911398780481159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42828394430396747949757 16060647911398780481159)
                    ·
                      rfl

theorem cell22_46917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_46917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46917 prefixEnd_46917 := by exact prefixLift 46917
  have htrace : WordTrace (prefixWord ++ tailWord_46917) baseStart_46917 baseEnd_46917 := by
    simpa [prefixWord, tailWord_46917, baseEnd_46917] using wordTrace_append hprefix tailTrace_46917
  have hstable : (prefixWord ++ tailWord_46917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46917).length < 2 ^ (prefixWord ++ tailWord_46917).sum := by decide
  have hdescent : baseEnd_46917 < baseStart_46917 := by decide
  rcases family_descends (prefixWord ++ tailWord_46917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46951 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 2, 3]
def baseStart_46951 : Nat := 118140960795 + 46951 * 2 ^ 59
def prefixEnd_46951 : Nat := 4983230072969 + 3 ^ 40 * 46951 * 2
def baseEnd_46951 : Nat := 16072286806234025131055

theorem tailTrace_46951 : CollatzResearch.WordTrace tailWord_46951 prefixEnd_46951 16072286806234025131055 := by
  unfold tailWord_46951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712443652912020437516707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1141629101941346958344471 1712443652912020437516707)
  ·
    refine ⟨2568665479368030656275061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1712443652912020437516707 2568665479368030656275061)
    ·
      refine ⟨240812388690752874025787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2568665479368030656275061 240812388690752874025787)
      ·
        refine ⟨361218583036129311038681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240812388690752874025787 361218583036129311038681)
        ·
          refine ⟨270913937277096983279011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361218583036129311038681 270913937277096983279011)
          ·
            refine ⟨406370905915645474918517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270913937277096983279011 406370905915645474918517)
            ·
              refine ⟨38097272429591763273611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406370905915645474918517 38097272429591763273611)
              ·
                refine ⟨57145908644387644910417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38097272429591763273611 57145908644387644910417)
                ·
                  refine ⟨42859431483290733682813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57145908644387644910417 42859431483290733682813)
                  ·
                    refine ⟨16072286806234025131055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42859431483290733682813 16072286806234025131055)
                    ·
                      rfl

theorem cell22_46951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_46951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46951 prefixEnd_46951 := by exact prefixLift 46951
  have htrace : WordTrace (prefixWord ++ tailWord_46951) baseStart_46951 baseEnd_46951 := by
    simpa [prefixWord, tailWord_46951, baseEnd_46951] using wordTrace_append hprefix tailTrace_46951
  have hstable : (prefixWord ++ tailWord_46951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46951).length < 2 ^ (prefixWord ++ tailWord_46951).sum := by decide
  have hdescent : baseEnd_46951 < baseStart_46951 := by decide
  rcases family_descends (prefixWord ++ tailWord_46951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46996 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_46996 : Nat := 118140960795 + 46996 * 2 ^ 59
def prefixEnd_46996 : Nat := 4983230072969 + 3 ^ 40 * 46996 * 2
def baseEnd_46996 : Nat := 16087691225868907755917

theorem tailTrace_46996 : CollatzResearch.WordTrace tailWord_46996 prefixEnd_46996 16087691225868907755917 := by
  unfold tailWord_46996
  simp only [CollatzResearch.WordTrace]
  refine ⟨857042468874496561452421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1142723291832662081936561 857042468874496561452421)
  ·
    refine ⟨160695462913968105272329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 857042468874496561452421 160695462913968105272329)
    ·
      refine ⟨120521597185476078954247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160695462913968105272329 120521597185476078954247)
      ·
        refine ⟨180782395778214118431371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120521597185476078954247 180782395778214118431371)
        ·
          refine ⟨271173593667321177647057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180782395778214118431371 271173593667321177647057)
          ·
            refine ⟨203380195250490883235293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271173593667321177647057 203380195250490883235293)
            ·
              refine ⟨76267573218934081213235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203380195250490883235293 76267573218934081213235)
              ·
                refine ⟨114401359828401121819853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76267573218934081213235 114401359828401121819853)
                ·
                  refine ⟨42900509935650420682445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114401359828401121819853 42900509935650420682445)
                  ·
                    refine ⟨16087691225868907755917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42900509935650420682445 16087691225868907755917)
                    ·
                      rfl

theorem cell22_46996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_46996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46996 prefixEnd_46996 := by exact prefixLift 46996
  have htrace : WordTrace (prefixWord ++ tailWord_46996) baseStart_46996 baseEnd_46996 := by
    simpa [prefixWord, tailWord_46996, baseEnd_46996] using wordTrace_append hprefix tailTrace_46996
  have hstable : (prefixWord ++ tailWord_46996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46996).length < 2 ^ (prefixWord ++ tailWord_46996).sum := by decide
  have hdescent : baseEnd_46996 < baseStart_46996 := by decide
  rcases family_descends (prefixWord ++ tailWord_46996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46998 : List Nat := [5, 3, 1, 1, 2, 1, 2, 7]
def baseStart_46998 : Nat := 118140960795 + 46998 * 2 ^ 59
def prefixEnd_46998 : Nat := 4983230072969 + 3 ^ 40 * 46998 * 2
def baseEnd_46998 : Nat := 1787597318526841022879

theorem tailTrace_46998 : CollatzResearch.WordTrace tailWord_46998 prefixEnd_46998 1787597318526841022879 := by
  unfold tailWord_46998
  simp only [CollatzResearch.WordTrace]
  refine ⟨107134867733859216529853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1142771922494498309651765 107134867733859216529853)
  ·
    refine ⟨40175575400197206198695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107134867733859216529853 40175575400197206198695)
    ·
      refine ⟨60263363100295809298043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40175575400197206198695 60263363100295809298043)
      ·
        refine ⟨90395044650443713947065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60263363100295809298043 90395044650443713947065)
        ·
          refine ⟨67796283487832785460299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90395044650443713947065 67796283487832785460299)
          ·
            refine ⟨101694425231749178190449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67796283487832785460299 101694425231749178190449)
            ·
              refine ⟨76270818923811883642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101694425231749178190449 76270818923811883642837)
              ·
                refine ⟨1787597318526841022879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76270818923811883642837 1787597318526841022879)
                ·
                  rfl

theorem cell22_46998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_46998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_46998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_46998 prefixEnd_46998 := by exact prefixLift 46998
  have htrace : WordTrace (prefixWord ++ tailWord_46998) baseStart_46998 baseEnd_46998 := by
    simpa [prefixWord, tailWord_46998, baseEnd_46998] using wordTrace_append hprefix tailTrace_46998
  have hstable : (prefixWord ++ tailWord_46998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46998).length < 2 ^ (prefixWord ++ tailWord_46998).sum := by decide
  have hdescent : baseEnd_46998 < baseStart_46998 := by decide
  rcases family_descends (prefixWord ++ tailWord_46998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47165 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_47165 : Nat := 118140960795 + 47165 * 2 ^ 59
def prefixEnd_47165 : Nat := 4983230072969 + 3 ^ 40 * 47165 * 2
def baseEnd_47165 : Nat := 16145543379608800280399

theorem tailTrace_47165 : CollatzResearch.WordTrace tailWord_47165 prefixEnd_47165 16145543379608800280399 := by
  unfold tailWord_47165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720248874136734985806949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1146832582757823323871299 1720248874136734985806949)
  ·
    refine ⟨322546663900637809838803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1720248874136734985806949 322546663900637809838803)
    ·
      refine ⟨483819995850956714758205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322546663900637809838803 483819995850956714758205)
      ·
        refine ⟨181432498444108768034327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483819995850956714758205 181432498444108768034327)
        ·
          refine ⟨272148747666163152051491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181432498444108768034327 272148747666163152051491)
          ·
            refine ⟨408223121499244728077237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272148747666163152051491 408223121499244728077237)
            ·
              refine ⟨38270917640554193257241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408223121499244728077237 38270917640554193257241)
              ·
                refine ⟨28703188230415644942931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38270917640554193257241 28703188230415644942931)
                ·
                  refine ⟨43054782345623467414397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28703188230415644942931 43054782345623467414397)
                  ·
                    refine ⟨16145543379608800280399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43054782345623467414397 16145543379608800280399)
                    ·
                      rfl

theorem cell22_47165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_47165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47165 prefixEnd_47165 := by exact prefixLift 47165
  have htrace : WordTrace (prefixWord ++ tailWord_47165) baseStart_47165 baseEnd_47165 := by
    simpa [prefixWord, tailWord_47165, baseEnd_47165] using wordTrace_append hprefix tailTrace_47165
  have hstable : (prefixWord ++ tailWord_47165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47165).length < 2 ^ (prefixWord ++ tailWord_47165).sum := by decide
  have hdescent : baseEnd_47165 < baseStart_47165 := by decide
  rcases family_descends (prefixWord ++ tailWord_47165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47191 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 1, 4]
def baseStart_47191 : Nat := 118140960795 + 47191 * 2 ^ 59
def prefixEnd_47191 : Nat := 4983230072969 + 3 ^ 40 * 47191 * 2
def baseEnd_47191 : Nat := 16154443710953399130319

theorem tailTrace_47191 : CollatzResearch.WordTrace tailWord_47191 prefixEnd_47191 16154443710953399130319 := by
  unfold tailWord_47191
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721197172042541426253427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1147464781361694284168951 1721197172042541426253427)
  ·
    refine ⟨2581795758063812139380141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721197172042541426253427 2581795758063812139380141)
    ·
      refine ⟨968173409273929552267553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2581795758063812139380141 968173409273929552267553)
      ·
        refine ⟨726130056955447164200665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968173409273929552267553 726130056955447164200665)
        ·
          refine ⟨544597542716585373150499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726130056955447164200665 544597542716585373150499)
          ·
            refine ⟨816896314074878059725749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544597542716585373150499 816896314074878059725749)
            ·
              refine ⟨76584029444519818099289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 816896314074878059725749 76584029444519818099289)
              ·
                refine ⟨57438022083389863574467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76584029444519818099289 57438022083389863574467)
                ·
                  refine ⟨86157033125084795361701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57438022083389863574467 86157033125084795361701)
                  ·
                    refine ⟨16154443710953399130319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86157033125084795361701 16154443710953399130319)
                    ·
                      rfl

theorem cell22_47191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_47191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47191 prefixEnd_47191 := by exact prefixLift 47191
  have htrace : WordTrace (prefixWord ++ tailWord_47191) baseStart_47191 baseEnd_47191 := by
    simpa [prefixWord, tailWord_47191, baseEnd_47191] using wordTrace_append hprefix tailTrace_47191
  have hstable : (prefixWord ++ tailWord_47191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47191).length < 2 ^ (prefixWord ++ tailWord_47191).sum := by decide
  have hdescent : baseEnd_47191 < baseStart_47191 := by decide
  rcases family_descends (prefixWord ++ tailWord_47191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47204 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_47204 : Nat := 118140960795 + 47204 * 2 ^ 59
def prefixEnd_47204 : Nat := 4983230072969 + 3 ^ 40 * 47204 * 2
def baseEnd_47204 : Nat := 16158893876625698555279

theorem tailTrace_47204 : CollatzResearch.WordTrace tailWord_47204 prefixEnd_47204 16158893876625698555279 := by
  unfold tailWord_47204
  simp only [CollatzResearch.WordTrace]
  refine ⟨860835660497722323238333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1147780880663629764317777 860835660497722323238333)
  ·
    refine ⟨322813372686645871214375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 860835660497722323238333 322813372686645871214375)
    ·
      refine ⟨484220059029968806821563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322813372686645871214375 484220059029968806821563)
      ·
        refine ⟨726330088544953210232345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484220059029968806821563 726330088544953210232345)
        ·
          refine ⟨544747566408714907674259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726330088544953210232345 544747566408714907674259)
          ·
            refine ⟨817121349613072361511389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544747566408714907674259 817121349613072361511389)
            ·
              refine ⟨306420506104902135566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817121349613072361511389 306420506104902135566771)
              ·
                refine ⟨459630759157353203350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306420506104902135566771 459630759157353203350157)
                ·
                  refine ⟨172361534684007451256309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459630759157353203350157 172361534684007451256309)
                  ·
                    refine ⟨16158893876625698555279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172361534684007451256309 16158893876625698555279)
                    ·
                      rfl

theorem cell22_47204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_47204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47204 prefixEnd_47204 := by exact prefixLift 47204
  have htrace : WordTrace (prefixWord ++ tailWord_47204) baseStart_47204 baseEnd_47204 := by
    simpa [prefixWord, tailWord_47204, baseEnd_47204] using wordTrace_append hprefix tailTrace_47204
  have hstable : (prefixWord ++ tailWord_47204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47204).length < 2 ^ (prefixWord ++ tailWord_47204).sum := by decide
  have hdescent : baseEnd_47204 < baseStart_47204 := by decide
  rcases family_descends (prefixWord ++ tailWord_47204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47223 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 4]
def baseStart_47223 : Nat := 118140960795 + 47223 * 2 ^ 59
def prefixEnd_47223 : Nat := 4983230072969 + 3 ^ 40 * 47223 * 2
def baseEnd_47223 : Nat := 5388465988305327443407

theorem tailTrace_47223 : CollatzResearch.WordTrace tailWord_47223 prefixEnd_47223 5388465988305327443407 := by
  unfold tailWord_47223
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722364307926610891418323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1148242871951073927612215 1722364307926610891418323)
  ·
    refine ⟨2583546461889916337127485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1722364307926610891418323 2583546461889916337127485)
    ·
      refine ⟨968829923208718626422807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2583546461889916337127485 968829923208718626422807)
      ·
        refine ⟨1453244884813077939634211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968829923208718626422807 1453244884813077939634211)
        ·
          refine ⟨2179867327219616909451317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453244884813077939634211 2179867327219616909451317)
          ·
            refine ⟨204362561926839085261061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2179867327219616909451317 204362561926839085261061)
            ·
              refine ⟨38317980361282328486449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204362561926839085261061 38317980361282328486449)
              ·
                refine ⟨28738485270961746364837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38317980361282328486449 28738485270961746364837)
                ·
                  refine ⟨5388465988305327443407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28738485270961746364837 5388465988305327443407)
                  ·
                    rfl

theorem cell22_47223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 4].length) (baseStart_47223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47223 prefixEnd_47223 := by exact prefixLift 47223
  have htrace : WordTrace (prefixWord ++ tailWord_47223) baseStart_47223 baseEnd_47223 := by
    simpa [prefixWord, tailWord_47223, baseEnd_47223] using wordTrace_append hprefix tailTrace_47223
  have hstable : (prefixWord ++ tailWord_47223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47223).length < 2 ^ (prefixWord ++ tailWord_47223).sum := by decide
  have hdescent : baseEnd_47223 < baseStart_47223 := by decide
  rcases family_descends (prefixWord ++ tailWord_47223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47386 : List Nat := [3, 1, 1, 3, 4, 10]
def baseStart_47386 : Nat := 118140960795 + 47386 * 2 ^ 59
def prefixEnd_47386 : Nat := 4983230072969 + 3 ^ 40 * 47386 * 2
def baseEnd_47386 : Nat := 200261681432566549441

theorem tailTrace_47386 : CollatzResearch.WordTrace tailWord_47386 prefixEnd_47386 200261681432566549441 := by
  unfold tailWord_47386
  simp only [CollatzResearch.WordTrace]
  refine ⟨432077351584022432400503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1152206270890726486401341 432077351584022432400503)
  ·
    refine ⟨648116027376033648600755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432077351584022432400503 648116027376033648600755)
    ·
      refine ⟨972174041064050472901133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648116027376033648600755 972174041064050472901133)
      ·
        refine ⟨364565265399018927337925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 972174041064050472901133 364565265399018927337925)
        ·
          refine ⟨68355987262316048875861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364565265399018927337925 68355987262316048875861)
          ·
            refine ⟨200261681432566549441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 68355987262316048875861 200261681432566549441)
            ·
              rfl

theorem cell22_47386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 10].length) (baseStart_47386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47386 prefixEnd_47386 := by exact prefixLift 47386
  have htrace : WordTrace (prefixWord ++ tailWord_47386) baseStart_47386 baseEnd_47386 := by
    simpa [prefixWord, tailWord_47386, baseEnd_47386] using wordTrace_append hprefix tailTrace_47386
  have hstable : (prefixWord ++ tailWord_47386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47386).length < 2 ^ (prefixWord ++ tailWord_47386).sum := by decide
  have hdescent : baseEnd_47386 < baseStart_47386 := by decide
  rcases family_descends (prefixWord ++ tailWord_47386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47392 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_47392 : Nat := 118140960795 + 47392 * 2 ^ 59
def prefixEnd_47392 : Nat := 4983230072969 + 3 ^ 40 * 47392 * 2
def baseEnd_47392 : Nat := 5407750039551958284901

theorem tailTrace_47392 : CollatzResearch.WordTrace tailWord_47392 prefixEnd_47392 5407750039551958284901 := by
  unfold tailWord_47392
  simp only [CollatzResearch.WordTrace]
  refine ⟨864264122157176377160215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1152352162876235169546953 864264122157176377160215)
  ·
    refine ⟨1296396183235764565740323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864264122157176377160215 1296396183235764565740323)
    ·
      refine ⟨1944594274853646848610485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296396183235764565740323 1944594274853646848610485)
      ·
        refine ⟨182305713267529392057233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1944594274853646848610485 182305713267529392057233)
        ·
          refine ⟨136729284950647044042925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182305713267529392057233 136729284950647044042925)
          ·
            refine ⟨51273481856492641516097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136729284950647044042925 51273481856492641516097)
            ·
              refine ⟨38455111392369481137073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51273481856492641516097 38455111392369481137073)
              ·
                refine ⟨28841333544277110852805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38455111392369481137073 28841333544277110852805)
                ·
                  refine ⟨5407750039551958284901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28841333544277110852805 5407750039551958284901)
                  ·
                    rfl

theorem cell22_47392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_47392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47392 prefixEnd_47392 := by exact prefixLift 47392
  have htrace : WordTrace (prefixWord ++ tailWord_47392) baseStart_47392 baseEnd_47392 := by
    simpa [prefixWord, tailWord_47392, baseEnd_47392] using wordTrace_append hprefix tailTrace_47392
  have hstable : (prefixWord ++ tailWord_47392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47392).length < 2 ^ (prefixWord ++ tailWord_47392).sum := by decide
  have hdescent : baseEnd_47392 < baseStart_47392 := by decide
  rcases family_descends (prefixWord ++ tailWord_47392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47418 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_47418 : Nat := 118140960795 + 47418 * 2 ^ 59
def prefixEnd_47418 : Nat := 4983230072969 + 3 ^ 40 * 47418 * 2
def baseEnd_47418 : Nat := 16232150450000473704623

theorem tailTrace_47418 : CollatzResearch.WordTrace tailWord_47418 prefixEnd_47418 16232150450000473704623 := by
  unfold tailWord_47418
  simp only [CollatzResearch.WordTrace]
  refine ⟨432369135555039798691727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1152984361480106129844605 432369135555039798691727)
  ·
    refine ⟨648553703332559698037591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432369135555039798691727 648553703332559698037591)
    ·
      refine ⟨972830554998839547056387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 648553703332559698037591 972830554998839547056387)
      ·
        refine ⟨1459245832498259320584581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972830554998839547056387 1459245832498259320584581)
        ·
          refine ⟨273608593593423622609609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1459245832498259320584581 273608593593423622609609)
          ·
            refine ⟨205206445195067716957207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273608593593423622609609 205206445195067716957207)
            ·
              refine ⟨307809667792601575435811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205206445195067716957207 307809667792601575435811)
              ·
                refine ⟨461714501688902363153717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307809667792601575435811 461714501688902363153717)
                ·
                  refine ⟨43285734533334596545661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461714501688902363153717 43285734533334596545661)
                  ·
                    refine ⟨16232150450000473704623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43285734533334596545661 16232150450000473704623)
                    ·
                      rfl

theorem cell22_47418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_47418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47418 prefixEnd_47418 := by exact prefixLift 47418
  have htrace : WordTrace (prefixWord ++ tailWord_47418) baseStart_47418 baseEnd_47418 := by
    simpa [prefixWord, tailWord_47418, baseEnd_47418] using wordTrace_append hprefix tailTrace_47418
  have hstable : (prefixWord ++ tailWord_47418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47418).length < 2 ^ (prefixWord ++ tailWord_47418).sum := by decide
  have hdescent : baseEnd_47418 < baseStart_47418 := by decide
  rcases family_descends (prefixWord ++ tailWord_47418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47431 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 7]
def baseStart_47431 : Nat := 118140960795 + 47431 * 2 ^ 59
def prefixEnd_47431 : Nat := 4983230072969 + 3 ^ 40 * 47431 * 2
def baseEnd_47431 : Nat := 5412200205224257709861

theorem tailTrace_47431 : CollatzResearch.WordTrace tailWord_47431 prefixEnd_47431 5412200205224257709861 := by
  unfold tailWord_47431
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729950691173062414990147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1153300460782041609993431 1729950691173062414990147)
  ·
    refine ⟨2594926036759593622485221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1729950691173062414990147 2594926036759593622485221)
    ·
      refine ⟨486548631892423804215979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2594926036759593622485221 486548631892423804215979)
      ·
        refine ⟨729822947838635706323969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486548631892423804215979 729822947838635706323969)
        ·
          refine ⟨547367210878976779742977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729822947838635706323969 547367210878976779742977)
          ·
            refine ⟨410525408159232584807233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547367210878976779742977 410525408159232584807233)
            ·
              refine ⟨307894056119424438605425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410525408159232584807233 307894056119424438605425)
              ·
                refine ⟨230920542089568328954069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307894056119424438605425 230920542089568328954069)
                ·
                  refine ⟨5412200205224257709861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 230920542089568328954069 5412200205224257709861)
                  ·
                    rfl

theorem cell22_47431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_47431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47431 prefixEnd_47431 := by exact prefixLift 47431
  have htrace : WordTrace (prefixWord ++ tailWord_47431) baseStart_47431 baseEnd_47431 := by
    simpa [prefixWord, tailWord_47431, baseEnd_47431] using wordTrace_append hprefix tailTrace_47431
  have hstable : (prefixWord ++ tailWord_47431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47431).length < 2 ^ (prefixWord ++ tailWord_47431).sum := by decide
  have hdescent : baseEnd_47431 < baseStart_47431 := by decide
  rcases family_descends (prefixWord ++ tailWord_47431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47463 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_47463 : Nat := 118140960795 + 47463 * 2 ^ 59
def prefixEnd_47463 : Nat := 4983230072969 + 3 ^ 40 * 47463 * 2
def baseEnd_47463 : Nat := 16247554869635356329485

theorem tailTrace_47463 : CollatzResearch.WordTrace tailWord_47463 prefixEnd_47463 16247554869635356329485 := by
  unfold tailWord_47463
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731117827057131880155043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1154078551371421253436695 1731117827057131880155043)
  ·
    refine ⟨2596676740585697820232565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1731117827057131880155043 2596676740585697820232565)
    ·
      refine ⟨243438444429909170646803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2596676740585697820232565 243438444429909170646803)
      ·
        refine ⟨365157666644863755970205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243438444429909170646803 365157666644863755970205)
        ·
          refine ⟨136934124991823908488827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365157666644863755970205 136934124991823908488827)
          ·
            refine ⟨205401187487735862733241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136934124991823908488827 205401187487735862733241)
            ·
              refine ⟨154050890615801897049931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205401187487735862733241 154050890615801897049931)
              ·
                refine ⟨231076335923702845574897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154050890615801897049931 231076335923702845574897)
                ·
                  refine ⟨173307251942777134181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231076335923702845574897 173307251942777134181173)
                  ·
                    refine ⟨16247554869635356329485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 173307251942777134181173 16247554869635356329485)
                    ·
                      rfl

theorem cell22_47463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_47463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47463 prefixEnd_47463 := by exact prefixLift 47463
  have htrace : WordTrace (prefixWord ++ tailWord_47463) baseStart_47463 baseEnd_47463 := by
    simpa [prefixWord, tailWord_47463, baseEnd_47463] using wordTrace_append hprefix tailTrace_47463
  have hstable : (prefixWord ++ tailWord_47463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47463).length < 2 ^ (prefixWord ++ tailWord_47463).sum := by decide
  have hdescent : baseEnd_47463 < baseStart_47463 := by decide
  rcases family_descends (prefixWord ++ tailWord_47463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47525 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_47525 : Nat := 118140960795 + 47525 * 2 ^ 59
def prefixEnd_47525 : Nat := 4983230072969 + 3 ^ 40 * 47525 * 2
def baseEnd_47525 : Nat := 16268778736687861279295

theorem tailTrace_47525 : CollatzResearch.WordTrace tailWord_47525 prefixEnd_47525 16268778736687861279295 := by
  unfold tailWord_47525
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733379152832516468912029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1155586101888344312608019 1733379152832516468912029)
  ·
    refine ⟨650017182312193675842011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1733379152832516468912029 650017182312193675842011)
    ·
      refine ⟨975025773468290513763017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650017182312193675842011 975025773468290513763017)
      ·
        refine ⟨731269330101217885322263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975025773468290513763017 731269330101217885322263)
        ·
          refine ⟨1096903995151826827983395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731269330101217885322263 1096903995151826827983395)
          ·
            refine ⟨1645355992727740241975093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096903995151826827983395 1645355992727740241975093)
            ·
              refine ⟨154252124318225647685165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1645355992727740241975093 154252124318225647685165)
              ·
                refine ⟨57844546619334617881937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154252124318225647685165 57844546619334617881937)
                ·
                  refine ⟨43383409964500963411453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57844546619334617881937 43383409964500963411453)
                  ·
                    refine ⟨16268778736687861279295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43383409964500963411453 16268778736687861279295)
                    ·
                      rfl

theorem cell22_47525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_47525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47525 prefixEnd_47525 := by exact prefixLift 47525
  have htrace : WordTrace (prefixWord ++ tailWord_47525) baseStart_47525 baseEnd_47525 := by
    simpa [prefixWord, tailWord_47525, baseEnd_47525] using wordTrace_append hprefix tailTrace_47525
  have hstable : (prefixWord ++ tailWord_47525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47525).length < 2 ^ (prefixWord ++ tailWord_47525).sum := by decide
  have hdescent : baseEnd_47525 < baseStart_47525 := by decide
  rcases family_descends (prefixWord ++ tailWord_47525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47587 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 3, 3]
def baseStart_47587 : Nat := 118140960795 + 47587 * 2 ^ 59
def prefixEnd_47587 : Nat := 4983230072969 + 3 ^ 40 * 47587 * 2
def baseEnd_47587 : Nat := 16290002603740366229105

theorem tailTrace_47587 : CollatzResearch.WordTrace tailWord_47587 prefixEnd_47587 16290002603740366229105 := by
  unfold tailWord_47587
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735640478607901057669015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1157093652405267371779343 1735640478607901057669015)
  ·
    refine ⟨2603460717911851586503523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735640478607901057669015 2603460717911851586503523)
    ·
      refine ⟨3905191076867777379755285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603460717911851586503523 3905191076867777379755285)
      ·
        refine ⟨183055831728177064676029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3905191076867777379755285 183055831728177064676029)
        ·
          refine ⟨68645936898066399253511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183055831728177064676029 68645936898066399253511)
          ·
            refine ⟨102968905347099598880267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68645936898066399253511 102968905347099598880267)
            ·
              refine ⟨154453358020649398320401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102968905347099598880267 154453358020649398320401)
              ·
                refine ⟨115840018515487048740301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154453358020649398320401 115840018515487048740301)
                ·
                  refine ⟨43440006943307643277613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115840018515487048740301 43440006943307643277613)
                  ·
                    refine ⟨16290002603740366229105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43440006943307643277613 16290002603740366229105)
                    ·
                      rfl

theorem cell22_47587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].length) (baseStart_47587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47587 prefixEnd_47587 := by exact prefixLift 47587
  have htrace : WordTrace (prefixWord ++ tailWord_47587) baseStart_47587 baseEnd_47587 := by
    simpa [prefixWord, tailWord_47587, baseEnd_47587] using wordTrace_append hprefix tailTrace_47587
  have hstable : (prefixWord ++ tailWord_47587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47587).length < 2 ^ (prefixWord ++ tailWord_47587).sum := by decide
  have hdescent : baseEnd_47587 < baseStart_47587 := by decide
  rcases family_descends (prefixWord ++ tailWord_47587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47617 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 5]
def baseStart_47617 : Nat := 118140960795 + 47617 * 2 ^ 59
def prefixEnd_47617 : Nat := 4983230072969 + 3 ^ 40 * 47617 * 2
def baseEnd_47617 : Nat := 5433424072276762659671

theorem tailTrace_47617 : CollatzResearch.WordTrace tailWord_47617 prefixEnd_47617 5433424072276762659671 := by
  unfold tailWord_47617
  simp only [CollatzResearch.WordTrace]
  refine ⟨1736734668499216181261105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1157823112332810787507403 1736734668499216181261105)
  ·
    refine ⟨1302551001374412135945829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1736734668499216181261105 1302551001374412135945829)
    ·
      refine ⟨244228312757702275489843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1302551001374412135945829 244228312757702275489843)
      ·
        refine ⟨366342469136553413234765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244228312757702275489843 366342469136553413234765)
        ·
          refine ⟨137378425926207529963037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366342469136553413234765 137378425926207529963037)
          ·
            refine ⟨51516909722327823736139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137378425926207529963037 51516909722327823736139)
            ·
              refine ⟨77275364583491735604209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51516909722327823736139 77275364583491735604209)
              ·
                refine ⟨57956523437618801703157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77275364583491735604209 57956523437618801703157)
                ·
                  refine ⟨5433424072276762659671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57956523437618801703157 5433424072276762659671)
                  ·
                    rfl

theorem cell22_47617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_47617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47617 prefixEnd_47617 := by exact prefixLift 47617
  have htrace : WordTrace (prefixWord ++ tailWord_47617) baseStart_47617 baseEnd_47617 := by
    simpa [prefixWord, tailWord_47617, baseEnd_47617] using wordTrace_append hprefix tailTrace_47617
  have hstable : (prefixWord ++ tailWord_47617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47617).length < 2 ^ (prefixWord ++ tailWord_47617).sum := by decide
  have hdescent : baseEnd_47617 < baseStart_47617 := by decide
  rcases family_descends (prefixWord ++ tailWord_47617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47645 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 6]
def baseStart_47645 : Nat := 118140960795 + 47645 * 2 ^ 59
def prefixEnd_47645 : Nat := 4983230072969 + 3 ^ 40 * 47645 * 2
def baseEnd_47645 : Nat := 5436619063015849426309

theorem tailTrace_47645 : CollatzResearch.WordTrace tailWord_47645 prefixEnd_47645 5436619063015849426309 := by
  unfold tailWord_47645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737755912397776963280389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1158503941598517975520259 1737755912397776963280389)
  ·
    refine ⟨325829233574583180615073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1737755912397776963280389 325829233574583180615073)
    ·
      refine ⟨244371925180937385461305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325829233574583180615073 244371925180937385461305)
      ·
        refine ⟨183278943885703039095979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244371925180937385461305 183278943885703039095979)
        ·
          refine ⟨274918415828554558643969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183278943885703039095979 274918415828554558643969)
          ·
            refine ⟨206188811871415918982977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274918415828554558643969 206188811871415918982977)
            ·
              refine ⟨154641608903561939237233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206188811871415918982977 154641608903561939237233)
              ·
                refine ⟨115981206677671454427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154641608903561939237233 115981206677671454427925)
                ·
                  refine ⟨5436619063015849426309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115981206677671454427925 5436619063015849426309)
                  ·
                    rfl

theorem cell22_47645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_47645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47645 prefixEnd_47645 := by exact prefixLift 47645
  have htrace : WordTrace (prefixWord ++ tailWord_47645) baseStart_47645 baseEnd_47645 := by
    simpa [prefixWord, tailWord_47645, baseEnd_47645] using wordTrace_append hprefix tailTrace_47645
  have hstable : (prefixWord ++ tailWord_47645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47645).length < 2 ^ (prefixWord ++ tailWord_47645).sum := by decide
  have hdescent : baseEnd_47645 < baseStart_47645 := by decide
  rcases family_descends (prefixWord ++ tailWord_47645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47655 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 1, 3]
def baseStart_47655 : Nat := 118140960795 + 47655 * 2 ^ 59
def prefixEnd_47655 : Nat := 4983230072969 + 3 ^ 40 * 47655 * 2
def baseEnd_47655 : Nat := 16313280393410855528897

theorem tailTrace_47655 : CollatzResearch.WordTrace tailWord_47655 prefixEnd_47655 16313280393410855528897 := by
  unfold tailWord_47655
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738120642361548671144419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1158747094907699114096279 1738120642361548671144419)
  ·
    refine ⟨2607180963542323006716629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1738120642361548671144419 2607180963542323006716629)
    ·
      refine ⟨61105803833023195469921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2607180963542323006716629 61105803833023195469921)
      ·
        refine ⟨45829352874767396602441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61105803833023195469921 45829352874767396602441)
        ·
          refine ⟨34372014656075547451831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45829352874767396602441 34372014656075547451831)
          ·
            refine ⟨51558021984113321177747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34372014656075547451831 51558021984113321177747)
            ·
              refine ⟨77337032976169981766621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51558021984113321177747 77337032976169981766621)
              ·
                refine ⟨29001387366063743162483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77337032976169981766621 29001387366063743162483)
                ·
                  refine ⟨43502081049095614743725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29001387366063743162483 43502081049095614743725)
                  ·
                    refine ⟨16313280393410855528897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43502081049095614743725 16313280393410855528897)
                    ·
                      rfl

theorem cell22_47655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_47655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47655 prefixEnd_47655 := by exact prefixLift 47655
  have htrace : WordTrace (prefixWord ++ tailWord_47655) baseStart_47655 baseEnd_47655 := by
    simpa [prefixWord, tailWord_47655, baseEnd_47655] using wordTrace_append hprefix tailTrace_47655
  have hstable : (prefixWord ++ tailWord_47655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47655).length < 2 ^ (prefixWord ++ tailWord_47655).sum := by decide
  have hdescent : baseEnd_47655 < baseStart_47655 := by decide
  rcases family_descends (prefixWord ++ tailWord_47655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47677 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_47677 : Nat := 118140960795 + 47677 * 2 ^ 59
def prefixEnd_47677 : Nat := 4983230072969 + 3 ^ 40 * 47677 * 2
def baseEnd_47677 : Nat := 16320811443010131478829

theorem tailTrace_47677 : CollatzResearch.WordTrace tailWord_47677 prefixEnd_47677 16320811443010131478829 := by
  unfold tailWord_47677
  simp only [CollatzResearch.WordTrace]
  refine ⟨1738923048281846428445285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1159282032187897618963523 1738923048281846428445285)
  ·
    refine ⟨326048071552846205333491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1738923048281846428445285 326048071552846205333491)
    ·
      refine ⟨489072107329269308000237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326048071552846205333491 489072107329269308000237)
      ·
        refine ⟨183402040248475990500089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489072107329269308000237 183402040248475990500089)
        ·
          refine ⟨137551530186356992875067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183402040248475990500089 137551530186356992875067)
          ·
            refine ⟨206327295279535489312601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137551530186356992875067 206327295279535489312601)
            ·
              refine ⟨154745471459651616984451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206327295279535489312601 154745471459651616984451)
              ·
                refine ⟨232118207189477425476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154745471459651616984451 232118207189477425476677)
                ·
                  refine ⟨43522163848027017276877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232118207189477425476677 43522163848027017276877)
                  ·
                    refine ⟨16320811443010131478829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43522163848027017276877 16320811443010131478829)
                    ·
                      rfl

theorem cell22_47677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_47677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47677 prefixEnd_47677 := by exact prefixLift 47677
  have htrace : WordTrace (prefixWord ++ tailWord_47677) baseStart_47677 baseEnd_47677 := by
    simpa [prefixWord, tailWord_47677, baseEnd_47677] using wordTrace_append hprefix tailTrace_47677
  have hstable : (prefixWord ++ tailWord_47677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47677).length < 2 ^ (prefixWord ++ tailWord_47677).sum := by decide
  have hdescent : baseEnd_47677 < baseStart_47677 := by decide
  rcases family_descends (prefixWord ++ tailWord_47677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47690 : List Nat := [3, 1, 2, 1, 1, 5, 2, 7]
def baseStart_47690 : Nat := 118140960795 + 47690 * 2 ^ 59
def prefixEnd_47690 : Nat := 4983230072969 + 3 ^ 40 * 47690 * 2
def baseEnd_47690 : Nat := 1813917956520270100421

theorem tailTrace_47690 : CollatzResearch.WordTrace tailWord_47690 prefixEnd_47690 1813917956520270100421 := by
  unfold tailWord_47690
  simp only [CollatzResearch.WordTrace]
  refine ⟨434849299308687412167131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1159598131489833099112349 434849299308687412167131)
  ·
    refine ⟨652273948963031118250697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434849299308687412167131 652273948963031118250697)
    ·
      refine ⟨489205461722273338688023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 652273948963031118250697 489205461722273338688023)
      ·
        refine ⟨733808192583410008032035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489205461722273338688023 733808192583410008032035)
        ·
          refine ⟨1100712288875115012048053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733808192583410008032035 1100712288875115012048053)
          ·
            refine ⟨103191777082042032379505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1100712288875115012048053 103191777082042032379505)
            ·
              refine ⟨77393832811531524284629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103191777082042032379505 77393832811531524284629)
              ·
                refine ⟨1813917956520270100421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77393832811531524284629 1813917956520270100421)
                ·
                  rfl

theorem cell22_47690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_47690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47690 prefixEnd_47690 := by exact prefixLift 47690
  have htrace : WordTrace (prefixWord ++ tailWord_47690) baseStart_47690 baseEnd_47690 := by
    simpa [prefixWord, tailWord_47690, baseEnd_47690] using wordTrace_append hprefix tailTrace_47690
  have hstable : (prefixWord ++ tailWord_47690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47690).length < 2 ^ (prefixWord ++ tailWord_47690).sum := by decide
  have hdescent : baseEnd_47690 < baseStart_47690 := by decide
  rcases family_descends (prefixWord ++ tailWord_47690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47694 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_47694 : Nat := 118140960795 + 47694 * 2 ^ 59
def prefixEnd_47694 : Nat := 4983230072969 + 3 ^ 40 * 47694 * 2
def baseEnd_47694 : Nat := 16326630890427753803777

theorem tailTrace_47694 : CollatzResearch.WordTrace tailWord_47694 prefixEnd_47694 16326630890427753803777 := by
  unfold tailWord_47694
  simp only [CollatzResearch.WordTrace]
  refine ⟨217442886152532291476767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1159695392813505554542757 217442886152532291476767)
  ·
    refine ⟨326164329228798437215151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217442886152532291476767 326164329228798437215151)
    ·
      refine ⟨489246493843197655822727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326164329228798437215151 489246493843197655822727)
      ·
        refine ⟨733869740764796483734091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489246493843197655822727 733869740764796483734091)
        ·
          refine ⟨1100804611147194725601137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733869740764796483734091 1100804611147194725601137)
          ·
            refine ⟨825603458360396044200853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100804611147194725601137 825603458360396044200853)
            ·
              refine ⟨38700162110643564571915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825603458360396044200853 38700162110643564571915)
              ·
                refine ⟨58050243165965346857873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38700162110643564571915 58050243165965346857873)
                ·
                  refine ⟨43537682374474010143405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58050243165965346857873 43537682374474010143405)
                  ·
                    refine ⟨16326630890427753803777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43537682374474010143405 16326630890427753803777)
                    ·
                      rfl

theorem cell22_47694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_47694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47694 prefixEnd_47694 := by exact prefixLift 47694
  have htrace : WordTrace (prefixWord ++ tailWord_47694) baseStart_47694 baseEnd_47694 := by
    simpa [prefixWord, tailWord_47694, baseEnd_47694] using wordTrace_append hprefix tailTrace_47694
  have hstable : (prefixWord ++ tailWord_47694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47694).length < 2 ^ (prefixWord ++ tailWord_47694).sum := by decide
  have hdescent : baseEnd_47694 < baseStart_47694 := by decide
  rcases family_descends (prefixWord ++ tailWord_47694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47735 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 5]
def baseStart_47735 : Nat := 118140960795 + 47735 * 2 ^ 59
def prefixEnd_47735 : Nat := 4983230072969 + 3 ^ 40 * 47735 * 2
def baseEnd_47735 : Nat := 5446888676105771176217

theorem tailTrace_47735 : CollatzResearch.WordTrace tailWord_47735 prefixEnd_47735 5446888676105771176217 := by
  unfold tailWord_47735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741038482071722334056659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1160692321381148222704439 1741038482071722334056659)
  ·
    refine ⟨2611557723107583501084989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1741038482071722334056659 2611557723107583501084989)
    ·
      refine ⟨979334146165343812906871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2611557723107583501084989 979334146165343812906871)
      ·
        refine ⟨1469001219248015719360307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979334146165343812906871 1469001219248015719360307)
        ·
          refine ⟨2203501828872023579040461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469001219248015719360307 2203501828872023579040461)
          ·
            refine ⟨826313185827008842140173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2203501828872023579040461 826313185827008842140173)
            ·
              refine ⟨309867444685128315802565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 826313185827008842140173 309867444685128315802565)
              ·
                refine ⟨58100145878461559212981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309867444685128315802565 58100145878461559212981)
                ·
                  refine ⟨5446888676105771176217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58100145878461559212981 5446888676105771176217)
                  ·
                    rfl

theorem cell22_47735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].length) (baseStart_47735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47735 prefixEnd_47735 := by exact prefixLift 47735
  have htrace : WordTrace (prefixWord ++ tailWord_47735) baseStart_47735 baseEnd_47735 := by
    simpa [prefixWord, tailWord_47735, baseEnd_47735] using wordTrace_append hprefix tailTrace_47735
  have hstable : (prefixWord ++ tailWord_47735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47735).length < 2 ^ (prefixWord ++ tailWord_47735).sum := by decide
  have hdescent : baseEnd_47735 < baseStart_47735 := by decide
  rcases family_descends (prefixWord ++ tailWord_47735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47780 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_47780 : Nat := 118140960795 + 47780 * 2 ^ 59
def prefixEnd_47780 : Nat := 4983230072969 + 3 ^ 40 * 47780 * 2
def baseEnd_47780 : Nat := 5452023482650732051171

theorem tailTrace_47780 : CollatzResearch.WordTrace tailWord_47780 prefixEnd_47780 5452023482650732051171 := by
  unfold tailWord_47780
  simp only [CollatzResearch.WordTrace]
  refine ⟨871339883454347509722397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1161786511272463346296529 871339883454347509722397)
  ·
    refine ⟨326752456295380316145899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 871339883454347509722397 326752456295380316145899)
    ·
      refine ⟨490128684443070474218849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326752456295380316145899 490128684443070474218849)
      ·
        refine ⟨367596513332302855664137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490128684443070474218849 367596513332302855664137)
        ·
          refine ⟨275697384999227141748103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367596513332302855664137 275697384999227141748103)
          ·
            refine ⟨413546077498840712622155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275697384999227141748103 413546077498840712622155)
            ·
              refine ⟨620319116248261068933233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413546077498840712622155 620319116248261068933233)
              ·
                refine ⟨465239337186195801699925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620319116248261068933233 465239337186195801699925)
                ·
                  refine ⟨5452023482650732051171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 465239337186195801699925 5452023482650732051171)
                  ·
                    rfl

theorem cell22_47780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_47780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47780 prefixEnd_47780 := by exact prefixLift 47780
  have htrace : WordTrace (prefixWord ++ tailWord_47780) baseStart_47780 baseEnd_47780 := by
    simpa [prefixWord, tailWord_47780, baseEnd_47780] using wordTrace_append hprefix tailTrace_47780
  have hstable : (prefixWord ++ tailWord_47780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47780).length < 2 ^ (prefixWord ++ tailWord_47780).sum := by decide
  have hdescent : baseEnd_47780 < baseStart_47780 := by decide
  rcases family_descends (prefixWord ++ tailWord_47780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47797 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 6]
def baseStart_47797 : Nat := 118140960795 + 47797 * 2 ^ 59
def prefixEnd_47797 : Nat := 4983230072969 + 3 ^ 40 * 47797 * 2
def baseEnd_47797 : Nat := 5453963298456606159487

theorem tailTrace_47797 : CollatzResearch.WordTrace tailWord_47797 prefixEnd_47797 5453963298456606159487 := by
  unfold tailWord_47797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743299807847106922813645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1162199871898071281875763 1743299807847106922813645)
  ·
    refine ⟨653737427942665096055117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1743299807847106922813645 653737427942665096055117)
    ·
      refine ⟨245151535478499411020669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 653737427942665096055117 245151535478499411020669)
      ·
        refine ⟨91931825804437279132751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245151535478499411020669 91931825804437279132751)
        ·
          refine ⟨137897738706655918699127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91931825804437279132751 137897738706655918699127)
          ·
            refine ⟨206846608059983878048691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137897738706655918699127 206846608059983878048691)
            ·
              refine ⟨310269912089975817073037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206846608059983878048691 310269912089975817073037)
              ·
                refine ⟨116351217033740931402389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310269912089975817073037 116351217033740931402389)
                ·
                  refine ⟨5453963298456606159487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116351217033740931402389 5453963298456606159487)
                  ·
                    rfl

theorem cell22_47797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_47797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47797 prefixEnd_47797 := by exact prefixLift 47797
  have htrace : WordTrace (prefixWord ++ tailWord_47797) baseStart_47797 baseEnd_47797 := by
    simpa [prefixWord, tailWord_47797, baseEnd_47797] using wordTrace_append hprefix tailTrace_47797
  have hstable : (prefixWord ++ tailWord_47797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47797).length < 2 ^ (prefixWord ++ tailWord_47797).sum := by decide
  have hdescent : baseEnd_47797 < baseStart_47797 := by decide
  rcases family_descends (prefixWord ++ tailWord_47797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47825 : List Nat := [1, 2, 2, 1, 2, 3, 3, 8]
def baseStart_47825 : Nat := 118140960795 + 47825 * 2 ^ 59
def prefixEnd_47825 : Nat := 4983230072969 + 3 ^ 40 * 47825 * 2
def baseEnd_47825 : Nat := 1819052763065230975375

theorem tailTrace_47825 : CollatzResearch.WordTrace tailWord_47825 prefixEnd_47825 1819052763065230975375 := by
  unfold tailWord_47825
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744321051745667704832929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1162880701163778469888619 1744321051745667704832929)
  ·
    refine ⟨1308240788809250778624697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1744321051745667704832929 1308240788809250778624697)
    ·
      refine ⟨981180591606938083968523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308240788809250778624697 981180591606938083968523)
      ·
        refine ⟨1471770887410407125952785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981180591606938083968523 1471770887410407125952785)
        ·
          refine ⟨1103828165557805344464589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471770887410407125952785 1103828165557805344464589)
          ·
            refine ⟨413935562084177004174221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103828165557805344464589 413935562084177004174221)
            ·
              refine ⟨155225835781566376565333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413935562084177004174221 155225835781566376565333)
              ·
                refine ⟨1819052763065230975375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 155225835781566376565333 1819052763065230975375)
                ·
                  rfl

theorem cell22_47825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 8].length) (baseStart_47825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47825 prefixEnd_47825 := by exact prefixLift 47825
  have htrace : WordTrace (prefixWord ++ tailWord_47825) baseStart_47825 baseEnd_47825 := by
    simpa [prefixWord, tailWord_47825, baseEnd_47825] using wordTrace_append hprefix tailTrace_47825
  have hstable : (prefixWord ++ tailWord_47825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47825).length < 2 ^ (prefixWord ++ tailWord_47825).sum := by decide
  have hdescent : baseEnd_47825 < baseStart_47825 := by decide
  rcases family_descends (prefixWord ++ tailWord_47825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47904 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_47904 : Nat := 118140960795 + 47904 * 2 ^ 59
def prefixEnd_47904 : Nat := 4983230072969 + 3 ^ 40 * 47904 * 2
def baseEnd_47904 : Nat := 5466172727352402017711

theorem tailTrace_47904 : CollatzResearch.WordTrace tailWord_47904 prefixEnd_47904 5466172727352402017711 := by
  unfold tailWord_47904
  simp only [CollatzResearch.WordTrace]
  refine ⟨873601209229732098479383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1164801612306309464639177 873601209229732098479383)
  ·
    refine ⟨1310401813844598147719075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873601209229732098479383 1310401813844598147719075)
    ·
      refine ⟨1965602720766897221578613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310401813844598147719075 1965602720766897221578613)
      ·
        refine ⟨184275255071896614522995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1965602720766897221578613 184275255071896614522995)
        ·
          refine ⟨276412882607844921784493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184275255071896614522995 276412882607844921784493)
          ·
            refine ⟨103654830977941845669185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 276412882607844921784493 103654830977941845669185)
            ·
              refine ⟨77741123233456384251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103654830977941845669185 77741123233456384251889)
              ·
                refine ⟨58305842425092288188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77741123233456384251889 58305842425092288188917)
                ·
                  refine ⟨5466172727352402017711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58305842425092288188917 5466172727352402017711)
                  ·
                    rfl

theorem cell22_47904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_47904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47904 prefixEnd_47904 := by exact prefixLift 47904
  have htrace : WordTrace (prefixWord ++ tailWord_47904) baseStart_47904 baseEnd_47904 := by
    simpa [prefixWord, tailWord_47904, baseEnd_47904] using wordTrace_append hprefix tailTrace_47904
  have hstable : (prefixWord ++ tailWord_47904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47904).length < 2 ^ (prefixWord ++ tailWord_47904).sum := by decide
  have hdescent : baseEnd_47904 < baseStart_47904 := by decide
  rcases family_descends (prefixWord ++ tailWord_47904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47908 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_47908 : Nat := 118140960795 + 47908 * 2 ^ 59
def prefixEnd_47908 : Nat := 4983230072969 + 3 ^ 40 * 47908 * 2
def baseEnd_47908 : Nat := 16399887463802528953121

theorem tailTrace_47908 : CollatzResearch.WordTrace tailWord_47908 prefixEnd_47908 16399887463802528953121 := by
  unfold tailWord_47908
  simp only [CollatzResearch.WordTrace]
  refine ⟨873674155222486440052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1164898873629981920069585 873674155222486440052189)
  ·
    refine ⟨327627808208432415019571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 873674155222486440052189 327627808208432415019571)
    ·
      refine ⟨491441712312648622529357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327627808208432415019571 491441712312648622529357)
      ·
        refine ⟨184290642117243233448509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491441712312648622529357 184290642117243233448509)
        ·
          refine ⟨69108990793966212543191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184290642117243233448509 69108990793966212543191)
          ·
            refine ⟨103663486190949318814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69108990793966212543191 103663486190949318814787)
            ·
              refine ⟨155495229286423978222181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103663486190949318814787 155495229286423978222181)
              ·
                refine ⟨29155355491204495916659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155495229286423978222181 29155355491204495916659)
                ·
                  refine ⟨43733033236806743874989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29155355491204495916659 43733033236806743874989)
                  ·
                    refine ⟨16399887463802528953121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43733033236806743874989 16399887463802528953121)
                    ·
                      rfl

theorem cell22_47908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_47908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47908 prefixEnd_47908 := by exact prefixLift 47908
  have htrace : WordTrace (prefixWord ++ tailWord_47908) baseStart_47908 baseEnd_47908 := by
    simpa [prefixWord, tailWord_47908, baseEnd_47908] using wordTrace_append hprefix tailTrace_47908
  have hstable : (prefixWord ++ tailWord_47908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47908).length < 2 ^ (prefixWord ++ tailWord_47908).sum := by decide
  have hdescent : baseEnd_47908 < baseStart_47908 := by decide
  rcases family_descends (prefixWord ++ tailWord_47908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47942 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_47942 : Nat := 118140960795 + 47942 * 2 ^ 59
def prefixEnd_47942 : Nat := 4983230072969 + 3 ^ 40 * 47942 * 2
def baseEnd_47942 : Nat := 16411526358637773603017

theorem tailTrace_47942 : CollatzResearch.WordTrace tailWord_47942 prefixEnd_47942 16411526358637773603017 := by
  unfold tailWord_47942
  simp only [CollatzResearch.WordTrace]
  refine ⟨54643387260056146463815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1165725594881197791228053 54643387260056146463815)
  ·
    refine ⟨81965080890084219695723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54643387260056146463815 81965080890084219695723)
    ·
      refine ⟨122947621335126329543585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81965080890084219695723 122947621335126329543585)
      ·
        refine ⟨92210716001344747157689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122947621335126329543585 92210716001344747157689)
        ·
          refine ⟨69158037001008560368267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92210716001344747157689 69158037001008560368267)
          ·
            refine ⟨103737055501512840552401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69158037001008560368267 103737055501512840552401)
            ·
              refine ⟨77802791626134630414301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103737055501512840552401 77802791626134630414301)
              ·
                refine ⟨29176046859800486405363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77802791626134630414301 29176046859800486405363)
                ·
                  refine ⟨43764070289700729608045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29176046859800486405363 43764070289700729608045)
                  ·
                    refine ⟨16411526358637773603017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43764070289700729608045 16411526358637773603017)
                    ·
                      rfl

theorem cell22_47942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_47942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_47942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_47942 prefixEnd_47942 := by exact prefixLift 47942
  have htrace : WordTrace (prefixWord ++ tailWord_47942) baseStart_47942 baseEnd_47942 := by
    simpa [prefixWord, tailWord_47942, baseEnd_47942] using wordTrace_append hprefix tailTrace_47942
  have hstable : (prefixWord ++ tailWord_47942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47942).length < 2 ^ (prefixWord ++ tailWord_47942).sum := by decide
  have hdescent : baseEnd_47942 < baseStart_47942 := by decide
  rcases family_descends (prefixWord ++ tailWord_47942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48067 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 8]
def baseStart_48067 : Nat := 118140960795 + 48067 * 2 ^ 59
def prefixEnd_48067 : Nat := 4983230072969 + 3 ^ 40 * 48067 * 2
def baseEnd_48067 : Nat := 5484772137726371409211

theorem tailTrace_48067 : CollatzResearch.WordTrace tailWord_48067 prefixEnd_48067 5484772137726371409211 := by
  unfold tailWord_48067
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753147516868943035142455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1168765011245962023428303 1753147516868943035142455)
  ·
    refine ⟨2629721275303414552713683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753147516868943035142455 2629721275303414552713683)
    ·
      refine ⟨3944581912955121829070525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629721275303414552713683 3944581912955121829070525)
      ·
        refine ⟨1479218217358170685901447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3944581912955121829070525 1479218217358170685901447)
        ·
          refine ⟨2218827326037256028852171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479218217358170685901447 2218827326037256028852171)
          ·
            refine ⟨3328240989055884043278257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218827326037256028852171 3328240989055884043278257)
            ·
              refine ⟨2496180741791913032458693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3328240989055884043278257 2496180741791913032458693)
              ·
                refine ⟨468033889085983693586005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2496180741791913032458693 468033889085983693586005)
                ·
                  refine ⟨5484772137726371409211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 468033889085983693586005 5484772137726371409211)
                  ·
                    rfl

theorem cell22_48067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_48067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48067 prefixEnd_48067 := by exact prefixLift 48067
  have htrace : WordTrace (prefixWord ++ tailWord_48067) baseStart_48067 baseEnd_48067 := by
    simpa [prefixWord, tailWord_48067, baseEnd_48067] using wordTrace_append hprefix tailTrace_48067
  have hstable : (prefixWord ++ tailWord_48067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48067).length < 2 ^ (prefixWord ++ tailWord_48067).sum := by decide
  have hdescent : baseEnd_48067 < baseStart_48067 := by decide
  rcases family_descends (prefixWord ++ tailWord_48067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48118 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_48118 : Nat := 118140960795 + 48118 * 2 ^ 59
def prefixEnd_48118 : Nat := 4983230072969 + 3 ^ 40 * 48118 * 2
def baseEnd_48118 : Nat := 5490591585143993734159

theorem tailTrace_48118 : CollatzResearch.WordTrace tailWord_48118 prefixEnd_48118 5490591585143993734159 := by
  unfold tailWord_48118
  simp only [CollatzResearch.WordTrace]
  refine ⟨109687977480261171578063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1170005093122785830166005 109687977480261171578063)
  ·
    refine ⟨164531966220391757367095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109687977480261171578063 164531966220391757367095)
    ·
      refine ⟨246797949330587636050643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164531966220391757367095 246797949330587636050643)
      ·
        refine ⟨370196923995881454075965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246797949330587636050643 370196923995881454075965)
        ·
          refine ⟨138823846498455545278487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370196923995881454075965 138823846498455545278487)
          ·
            refine ⟨208235769747683317917731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138823846498455545278487 208235769747683317917731)
            ·
              refine ⟨312353654621524976876597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208235769747683317917731 312353654621524976876597)
              ·
                refine ⟨29283155120767966582181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312353654621524976876597 29283155120767966582181)
                ·
                  refine ⟨5490591585143993734159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29283155120767966582181 5490591585143993734159)
                  ·
                    rfl

theorem cell22_48118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_48118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48118 prefixEnd_48118 := by exact prefixLift 48118
  have htrace : WordTrace (prefixWord ++ tailWord_48118) baseStart_48118 baseEnd_48118 := by
    simpa [prefixWord, tailWord_48118, baseEnd_48118] using wordTrace_append hprefix tailTrace_48118
  have hstable : (prefixWord ++ tailWord_48118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48118).length < 2 ^ (prefixWord ++ tailWord_48118).sum := by decide
  have hdescent : baseEnd_48118 < baseStart_48118 := by decide
  rcases family_descends (prefixWord ++ tailWord_48118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48129 : List Nat := [1, 2, 4, 1, 2, 3, 9]
def baseStart_48129 : Nat := 118140960795 + 48129 * 2 ^ 59
def prefixEnd_48129 : Nat := 4983230072969 + 3 ^ 40 * 48129 * 2
def baseEnd_48129 : Nat := 610205195564134043609

theorem tailTrace_48129 : CollatzResearch.WordTrace tailWord_48129 prefixEnd_48129 610205195564134043609 := by
  unfold tailWord_48129
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755408842644327623899441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1170272561762885082599627 1755408842644327623899441)
  ·
    refine ⟨1316556631983245717924581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1755408842644327623899441 1316556631983245717924581)
    ·
      refine ⟨246854368496858572110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1316556631983245717924581 246854368496858572110859)
      ·
        refine ⟨370281552745287858166289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246854368496858572110859 370281552745287858166289)
        ·
          refine ⟨277711164558965893624717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370281552745287858166289 277711164558965893624717)
          ·
            refine ⟨104141686709612210109269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277711164558965893624717 104141686709612210109269)
            ·
              refine ⟨610205195564134043609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 104141686709612210109269 610205195564134043609)
              ·
                rfl

theorem cell22_48129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 9].length) (baseStart_48129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48129 prefixEnd_48129 := by exact prefixLift 48129
  have htrace : WordTrace (prefixWord ++ tailWord_48129) baseStart_48129 baseEnd_48129 := by
    simpa [prefixWord, tailWord_48129, baseEnd_48129] using wordTrace_append hprefix tailTrace_48129
  have hstable : (prefixWord ++ tailWord_48129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48129).length < 2 ^ (prefixWord ++ tailWord_48129).sum := by decide
  have hdescent : baseEnd_48129 < baseStart_48129 := by decide
  rcases family_descends (prefixWord ++ tailWord_48129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48195 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 1, 3]
def baseStart_48195 : Nat := 118140960795 + 48195 * 2 ^ 59
def prefixEnd_48195 : Nat := 4983230072969 + 3 ^ 40 * 48195 * 2
def baseEnd_48195 : Nat := 16498133429029447027241

theorem tailTrace_48195 : CollatzResearch.WordTrace tailWord_48195 prefixEnd_48195 16498133429029447027241 := by
  unfold tailWord_48195
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757816060405220895802039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1171877373603480597201359 1757816060405220895802039)
  ·
    refine ⟨2636724090607831343703059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1757816060405220895802039 2636724090607831343703059)
    ·
      refine ⟨3955086135911747015554589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636724090607831343703059 3955086135911747015554589)
      ·
        refine ⟨1483157300966905130832971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3955086135911747015554589 1483157300966905130832971)
        ·
          refine ⟨2224735951450357696249457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483157300966905130832971 2224735951450357696249457)
          ·
            refine ⟨1668551963587768272187093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224735951450357696249457 1668551963587768272187093)
            ·
              refine ⟨39106686646588318879385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1668551963587768272187093 39106686646588318879385)
              ·
                refine ⟨29330014984941239159539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39106686646588318879385 29330014984941239159539)
                ·
                  refine ⟨43995022477411858739309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29330014984941239159539 43995022477411858739309)
                  ·
                    refine ⟨16498133429029447027241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43995022477411858739309 16498133429029447027241)
                    ·
                      rfl

theorem cell22_48195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 3].length) (baseStart_48195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48195 prefixEnd_48195 := by exact prefixLift 48195
  have htrace : WordTrace (prefixWord ++ tailWord_48195) baseStart_48195 baseEnd_48195 := by
    simpa [prefixWord, tailWord_48195, baseEnd_48195] using wordTrace_append hprefix tailTrace_48195
  have hstable : (prefixWord ++ tailWord_48195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48195).length < 2 ^ (prefixWord ++ tailWord_48195).sum := by decide
  have hdescent : baseEnd_48195 < baseStart_48195 := by decide
  rcases family_descends (prefixWord ++ tailWord_48195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48204 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_48204 : Nat := 118140960795 + 48204 * 2 ^ 59
def prefixEnd_48204 : Nat := 4983230072969 + 3 ^ 40 * 48204 * 2
def baseEnd_48204 : Nat := 16501214312956423552213

theorem tailTrace_48204 : CollatzResearch.WordTrace tailWord_48204 prefixEnd_48204 16501214312956423552213 := by
  unfold tailWord_48204
  simp only [CollatzResearch.WordTrace]
  refine ⟨879072158686307716439833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1172096211581743621919777 879072158686307716439833)
  ·
    refine ⟨659304119014730787329875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 879072158686307716439833 659304119014730787329875)
    ·
      refine ⟨988956178522096180994813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659304119014730787329875 988956178522096180994813)
      ·
        refine ⟨370858566945786067873055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 988956178522096180994813 370858566945786067873055)
        ·
          refine ⟨556287850418679101809583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370858566945786067873055 556287850418679101809583)
          ·
            refine ⟨834431775628018652714375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556287850418679101809583 834431775628018652714375)
            ·
              refine ⟨1251647663442027979071563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834431775628018652714375 1251647663442027979071563)
              ·
                refine ⟨1877471495163041968607345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251647663442027979071563 1877471495163041968607345)
                ·
                  refine ⟨1408103621372281476455509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877471495163041968607345 1408103621372281476455509)
                  ·
                    refine ⟨16501214312956423552213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1408103621372281476455509 16501214312956423552213)
                    ·
                      rfl

theorem cell22_48204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_48204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48204 prefixEnd_48204 := by exact prefixLift 48204
  have htrace : WordTrace (prefixWord ++ tailWord_48204) baseStart_48204 baseEnd_48204 := by
    simpa [prefixWord, tailWord_48204, baseEnd_48204] using wordTrace_append hprefix tailTrace_48204
  have hstable : (prefixWord ++ tailWord_48204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48204).length < 2 ^ (prefixWord ++ tailWord_48204).sum := by decide
  have hdescent : baseEnd_48204 < baseStart_48204 := by decide
  rcases family_descends (prefixWord ++ tailWord_48204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48251 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 4, 3]
def baseStart_48251 : Nat := 118140960795 + 48251 * 2 ^ 59
def prefixEnd_48251 : Nat := 4983230072969 + 3 ^ 40 * 48251 * 2
def baseEnd_48251 : Nat := 16517303373463967627069

theorem tailTrace_48251 : CollatzResearch.WordTrace tailWord_48251 prefixEnd_48251 16517303373463967627069 := by
  unfold tailWord_48251
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759858548202342459840607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173239032134894973227071 1759858548202342459840607)
  ·
    refine ⟨2639787822303513689760911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759858548202342459840607 2639787822303513689760911)
    ·
      refine ⟨3959681733455270534641367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639787822303513689760911 3959681733455270534641367)
      ·
        refine ⟨5939522600182905801962051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3959681733455270534641367 5939522600182905801962051)
        ·
          refine ⟨8909283900274358702943077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939522600182905801962051 8909283900274358702943077)
          ·
            refine ⟨1670490731301442256801827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8909283900274358702943077 1670490731301442256801827)
            ·
              refine ⟨2505736096952163385202741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670490731301442256801827 2505736096952163385202741)
              ·
                refine ⟨234912759089265317362757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2505736096952163385202741 234912759089265317362757)
                ·
                  refine ⟨44046142329237247005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234912759089265317362757 44046142329237247005517)
                  ·
                    refine ⟨16517303373463967627069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44046142329237247005517 16517303373463967627069)
                    ·
                      rfl

theorem cell22_48251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].length) (baseStart_48251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48251 prefixEnd_48251 := by exact prefixLift 48251
  have htrace : WordTrace (prefixWord ++ tailWord_48251) baseStart_48251 baseEnd_48251 := by
    simpa [prefixWord, tailWord_48251, baseEnd_48251] using wordTrace_append hprefix tailTrace_48251
  have hstable : (prefixWord ++ tailWord_48251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48251).length < 2 ^ (prefixWord ++ tailWord_48251).sum := by decide
  have hdescent : baseEnd_48251 < baseStart_48251 := by decide
  rcases family_descends (prefixWord ++ tailWord_48251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48253 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 4]
def baseStart_48253 : Nat := 118140960795 + 48253 * 2 ^ 59
def prefixEnd_48253 : Nat := 4983230072969 + 3 ^ 40 * 48253 * 2
def baseEnd_48253 : Nat := 5505996004778876359021

theorem tailTrace_48253 : CollatzResearch.WordTrace tailWord_48253 prefixEnd_48253 5505996004778876359021 := by
  unfold tailWord_48253
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759931494195096801413413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173287662796731200942275 1759931494195096801413413)
  ·
    refine ⟨329987155161580650265015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1759931494195096801413413 329987155161580650265015)
    ·
      refine ⟨494980732742370975397523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329987155161580650265015 494980732742370975397523)
      ·
        refine ⟨742471099113556463096285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494980732742370975397523 742471099113556463096285)
        ·
          refine ⟨278426662167583673661107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 742471099113556463096285 278426662167583673661107)
          ·
            refine ⟨417639993251375510491661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278426662167583673661107 417639993251375510491661)
            ·
              refine ⟨156614997469265816434373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417639993251375510491661 156614997469265816434373)
              ·
                refine ⟨29365312025487340581445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156614997469265816434373 29365312025487340581445)
                ·
                  refine ⟨5505996004778876359021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29365312025487340581445 5505996004778876359021)
                  ·
                    rfl

theorem cell22_48253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_48253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48253 prefixEnd_48253 := by exact prefixLift 48253
  have htrace : WordTrace (prefixWord ++ tailWord_48253) baseStart_48253 baseEnd_48253 := by
    simpa [prefixWord, tailWord_48253, baseEnd_48253] using wordTrace_append hprefix tailTrace_48253
  have hstable : (prefixWord ++ tailWord_48253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48253).length < 2 ^ (prefixWord ++ tailWord_48253).sum := by decide
  have hdescent : baseEnd_48253 < baseStart_48253 := by decide
  rcases family_descends (prefixWord ++ tailWord_48253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48266 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_48266 : Nat := 118140960795 + 48266 * 2 ^ 59
def prefixEnd_48266 : Nat := 4983230072969 + 3 ^ 40 * 48266 * 2
def baseEnd_48266 : Nat := 16522438180008928502023

theorem tailTrace_48266 : CollatzResearch.WordTrace tailWord_48266 prefixEnd_48266 16522438180008928502023 := by
  unfold tailWord_48266
  simp only [CollatzResearch.WordTrace]
  refine ⟨440101410787000005409163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1173603762098666681091101 440101410787000005409163)
  ·
    refine ⟨660152116180500008113745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440101410787000005409163 660152116180500008113745)
    ·
      refine ⟨495114087135375006085309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660152116180500008113745 495114087135375006085309)
      ·
        refine ⟨185667782675765627281991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495114087135375006085309 185667782675765627281991)
        ·
          refine ⟨278501674013648440922987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185667782675765627281991 278501674013648440922987)
          ·
            refine ⟨417752511020472661384481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278501674013648440922987 417752511020472661384481)
            ·
              refine ⟨313314383265354496038361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417752511020472661384481 313314383265354496038361)
              ·
                refine ⟨234985787449015872028771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313314383265354496038361 234985787449015872028771)
                ·
                  refine ⟨352478681173523808043157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234985787449015872028771 352478681173523808043157)
                  ·
                    refine ⟨16522438180008928502023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 352478681173523808043157 16522438180008928502023)
                    ·
                      rfl

theorem cell22_48266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_48266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48266 prefixEnd_48266 := by exact prefixLift 48266
  have htrace : WordTrace (prefixWord ++ tailWord_48266) baseStart_48266 baseEnd_48266 := by
    simpa [prefixWord, tailWord_48266, baseEnd_48266] using wordTrace_append hprefix tailTrace_48266
  have hstable : (prefixWord ++ tailWord_48266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48266).length < 2 ^ (prefixWord ++ tailWord_48266).sum := by decide
  have hdescent : baseEnd_48266 < baseStart_48266 := by decide
  rcases family_descends (prefixWord ++ tailWord_48266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48298 : List Nat := [3, 1, 5, 1, 1, 2, 9]
def baseStart_48298 : Nat := 118140960795 + 48298 * 2 ^ 59
def prefixEnd_48298 : Nat := 4983230072969 + 3 ^ 40 * 48298 * 2
def baseEnd_48298 : Nat := 612347867924870803775

theorem tailTrace_48298 : CollatzResearch.WordTrace tailWord_48298 prefixEnd_48298 612347867924870803775 := by
  unfold tailWord_48298
  simp only [CollatzResearch.WordTrace]
  refine ⟨440393194758017371700387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1174381852688046324534365 440393194758017371700387)
  ·
    refine ⟨660589792137026057550581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440393194758017371700387 660589792137026057550581)
    ·
      refine ⟨61930293012846192895367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 660589792137026057550581 61930293012846192895367)
      ·
        refine ⟨92895439519269289343051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61930293012846192895367 92895439519269289343051)
        ·
          refine ⟨139343159278903934014577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92895439519269289343051 139343159278903934014577)
          ·
            refine ⟨104507369459177950510933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139343159278903934014577 104507369459177950510933)
            ·
              refine ⟨612347867924870803775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 104507369459177950510933 612347867924870803775)
              ·
                rfl

theorem cell22_48298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 9].length) (baseStart_48298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48298 prefixEnd_48298 := by exact prefixLift 48298
  have htrace : WordTrace (prefixWord ++ tailWord_48298) baseStart_48298 baseEnd_48298 := by
    simpa [prefixWord, tailWord_48298, baseEnd_48298] using wordTrace_append hprefix tailTrace_48298
  have hstable : (prefixWord ++ tailWord_48298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48298).length < 2 ^ (prefixWord ++ tailWord_48298).sum := by decide
  have hdescent : baseEnd_48298 < baseStart_48298 := by decide
  rcases family_descends (prefixWord ++ tailWord_48298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48313 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_48313 : Nat := 118140960795 + 48313 * 2 ^ 59
def prefixEnd_48313 : Nat := 4983230072969 + 3 ^ 40 * 48313 * 2
def baseEnd_48313 : Nat := 16538527240516472576879

theorem tailTrace_48313 : CollatzResearch.WordTrace tailWord_48313 prefixEnd_48313 16538527240516472576879 := by
  unfold tailWord_48313
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762119873977727048597593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1174746582651818032398395 1762119873977727048597593)
  ·
    refine ⟨1321589905483295286448195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1762119873977727048597593 1321589905483295286448195)
    ·
      refine ⟨1982384858224942929672293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321589905483295286448195 1982384858224942929672293)
      ·
        refine ⟨371697160917176799313555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1982384858224942929672293 371697160917176799313555)
        ·
          refine ⟨557545741375765198970333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371697160917176799313555 557545741375765198970333)
          ·
            refine ⟨209079653015911949613875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557545741375765198970333 209079653015911949613875)
            ·
              refine ⟨313619479523867924420813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209079653015911949613875 313619479523867924420813)
              ·
                refine ⟨117607304821450471657805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313619479523867924420813 117607304821450471657805)
                ·
                  refine ⟨44102739308043926871677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117607304821450471657805 44102739308043926871677)
                  ·
                    refine ⟨16538527240516472576879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44102739308043926871677 16538527240516472576879)
                    ·
                      rfl

theorem cell22_48313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_48313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48313 prefixEnd_48313 := by exact prefixLift 48313
  have htrace : WordTrace (prefixWord ++ tailWord_48313) baseStart_48313 baseEnd_48313 := by
    simpa [prefixWord, tailWord_48313, baseEnd_48313] using wordTrace_append hprefix tailTrace_48313
  have hstable : (prefixWord ++ tailWord_48313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48313).length < 2 ^ (prefixWord ++ tailWord_48313).sum := by decide
  have hdescent : baseEnd_48313 < baseStart_48313 := by decide
  rcases family_descends (prefixWord ++ tailWord_48313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48416 : List Nat := [2, 1, 1, 5, 13]
def baseStart_48416 : Nat := 118140960795 + 48416 * 2 ^ 59
def prefixEnd_48416 : Nat := 4983230072969 + 3 ^ 40 * 48416 * 2
def baseEnd_48416 : Nat := 68204881668553651241

theorem tailTrace_48416 : CollatzResearch.WordTrace tailWord_48416 prefixEnd_48416 68204881668553651241 := by
  unfold tailWord_48416
  simp only [CollatzResearch.WordTrace]
  refine ⟨882938296302287819798551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1177251061736383759731401 882938296302287819798551)
  ·
    refine ⟨1324407444453431729697827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882938296302287819798551 1324407444453431729697827)
    ·
      refine ⟨1986611166680147594546741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324407444453431729697827 1986611166680147594546741)
      ·
        refine ⟨186244796876263836988757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1986611166680147594546741 186244796876263836988757)
        ·
          refine ⟨68204881668553651241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 186244796876263836988757 68204881668553651241)
          ·
            rfl

theorem cell22_48416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 13].length) (baseStart_48416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48416 prefixEnd_48416 := by exact prefixLift 48416
  have htrace : WordTrace (prefixWord ++ tailWord_48416) baseStart_48416 baseEnd_48416 := by
    simpa [prefixWord, tailWord_48416, baseEnd_48416] using wordTrace_append hprefix tailTrace_48416
  have hstable : (prefixWord ++ tailWord_48416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48416).length < 2 ^ (prefixWord ++ tailWord_48416).sum := by decide
  have hdescent : baseEnd_48416 < baseStart_48416 := by decide
  rcases family_descends (prefixWord ++ tailWord_48416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48431 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_48431 : Nat := 118140960795 + 48431 * 2 ^ 59
def prefixEnd_48431 : Nat := 4983230072969 + 3 ^ 40 * 48431 * 2
def baseEnd_48431 : Nat := 16578921052003498126517

theorem tailTrace_48431 : CollatzResearch.WordTrace tailWord_48431 prefixEnd_48431 16578921052003498126517 := by
  unfold tailWord_48431
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766423687550233201393147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1177615791700155467595431 1766423687550233201393147)
  ·
    refine ⟨2649635531325349802089721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1766423687550233201393147 2649635531325349802089721)
    ·
      refine ⟨1987226648494012351567291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2649635531325349802089721 1987226648494012351567291)
      ·
        refine ⟨2980839972741018527350937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987226648494012351567291 2980839972741018527350937)
        ·
          refine ⟨2235629979555763895513203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980839972741018527350937 2235629979555763895513203)
          ·
            refine ⟨3353444969333645843269805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235629979555763895513203 3353444969333645843269805)
            ·
              refine ⟨1257541863500117191226177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353444969333645843269805 1257541863500117191226177)
              ·
                refine ⟨943156397625087893419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257541863500117191226177 943156397625087893419633)
                ·
                  refine ⟨707367298218815920064725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943156397625087893419633 707367298218815920064725)
                  ·
                    refine ⟨16578921052003498126517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 707367298218815920064725 16578921052003498126517)
                    ·
                      rfl

theorem cell22_48431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_48431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48431 prefixEnd_48431 := by exact prefixLift 48431
  have htrace : WordTrace (prefixWord ++ tailWord_48431) baseStart_48431 baseEnd_48431 := by
    simpa [prefixWord, tailWord_48431, baseEnd_48431] using wordTrace_append hprefix tailTrace_48431
  have hstable : (prefixWord ++ tailWord_48431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48431).length < 2 ^ (prefixWord ++ tailWord_48431).sum := by decide
  have hdescent : baseEnd_48431 < baseStart_48431 := by decide
  rcases family_descends (prefixWord ++ tailWord_48431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48433 : List Nat := [1, 2, 2, 3, 3, 1, 3, 7]
def baseStart_48433 : Nat := 118140960795 + 48433 * 2 ^ 59
def prefixEnd_48433 : Nat := 4983230072969 + 3 ^ 40 * 48433 * 2
def baseEnd_48433 : Nat := 1842178410319573286279

theorem tailTrace_48433 : CollatzResearch.WordTrace tailWord_48433 prefixEnd_48433 1842178410319573286279 := by
  unfold tailWord_48433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1766496633542987542965953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1177664422361991695310635 1766496633542987542965953)
  ·
    refine ⟨1324872475157240657224465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1766496633542987542965953 1324872475157240657224465)
    ·
      refine ⟨993654356367930492918349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1324872475157240657224465 993654356367930492918349)
      ·
        refine ⟨372620383637973934844381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 993654356367930492918349 372620383637973934844381)
        ·
          refine ⟨139732643864240225566643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 372620383637973934844381 139732643864240225566643)
          ·
            refine ⟨209598965796360338349965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139732643864240225566643 209598965796360338349965)
            ·
              refine ⟨78599612173635126881237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209598965796360338349965 78599612173635126881237)
              ·
                refine ⟨1842178410319573286279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78599612173635126881237 1842178410319573286279)
                ·
                  rfl

theorem cell22_48433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 7].length) (baseStart_48433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48433 prefixEnd_48433 := by exact prefixLift 48433
  have htrace : WordTrace (prefixWord ++ tailWord_48433) baseStart_48433 baseEnd_48433 := by
    simpa [prefixWord, tailWord_48433, baseEnd_48433] using wordTrace_append hprefix tailTrace_48433
  have hstable : (prefixWord ++ tailWord_48433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48433).length < 2 ^ (prefixWord ++ tailWord_48433).sum := by decide
  have hdescent : baseEnd_48433 < baseStart_48433 := by decide
  rcases family_descends (prefixWord ++ tailWord_48433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48452 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_48452 : Nat := 118140960795 + 48452 * 2 ^ 59
def prefixEnd_48452 : Nat := 4983230072969 + 3 ^ 40 * 48452 * 2
def baseEnd_48452 : Nat := 16586109781166443351453

theorem tailTrace_48452 : CollatzResearch.WordTrace tailWord_48452 prefixEnd_48452 16586109781166443351453 := by
  unfold tailWord_48452
  simp only [CollatzResearch.WordTrace]
  refine ⟨883594810237076893953805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1178126413649435858605073 883594810237076893953805)
  ·
    refine ⟨331348053838903835232677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 883594810237076893953805 331348053838903835232677)
    ·
      refine ⟨62127760094794469106127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 331348053838903835232677 62127760094794469106127)
      ·
        refine ⟨93191640142191703659191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62127760094794469106127 93191640142191703659191)
        ·
          refine ⟨139787460213287555488787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93191640142191703659191 139787460213287555488787)
          ·
            refine ⟨209681190319931333233181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139787460213287555488787 209681190319931333233181)
            ·
              refine ⟨78630446369974249962443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209681190319931333233181 78630446369974249962443)
              ·
                refine ⟨117945669554961374943665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78630446369974249962443 117945669554961374943665)
                ·
                  refine ⟨88459252166221031207749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117945669554961374943665 88459252166221031207749)
                  ·
                    refine ⟨16586109781166443351453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88459252166221031207749 16586109781166443351453)
                    ·
                      rfl

theorem cell22_48452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_48452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48452 prefixEnd_48452 := by exact prefixLift 48452
  have htrace : WordTrace (prefixWord ++ tailWord_48452) baseStart_48452 baseEnd_48452 := by
    simpa [prefixWord, tailWord_48452, baseEnd_48452] using wordTrace_append hprefix tailTrace_48452
  have hstable : (prefixWord ++ tailWord_48452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48452).length < 2 ^ (prefixWord ++ tailWord_48452).sum := by decide
  have hdescent : baseEnd_48452 < baseStart_48452 := by decide
  rcases family_descends (prefixWord ++ tailWord_48452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48482 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_48482 : Nat := 118140960795 + 48482 * 2 ^ 59
def prefixEnd_48482 : Nat := 4983230072969 + 3 ^ 40 * 48482 * 2
def baseEnd_48482 : Nat := 16596379394256365101361

theorem tailTrace_48482 : CollatzResearch.WordTrace tailWord_48482 prefixEnd_48482 16596379394256365101361 := by
  unfold tailWord_48482
  simp only [CollatzResearch.WordTrace]
  refine ⟨442070952591367227874925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1178855873576979274333133 442070952591367227874925)
  ·
    refine ⟨165776607221762710453097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 442070952591367227874925 165776607221762710453097)
    ·
      refine ⟨124332455416322032839823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165776607221762710453097 124332455416322032839823)
      ·
        refine ⟨186498683124483049259735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124332455416322032839823 186498683124483049259735)
        ·
          refine ⟨279748024686724573889603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186498683124483049259735 279748024686724573889603)
          ·
            refine ⟨419622037030086860834405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279748024686724573889603 419622037030086860834405)
            ·
              refine ⟨78679131943141286406451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419622037030086860834405 78679131943141286406451)
              ·
                refine ⟨118018697914711929609677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78679131943141286406451 118018697914711929609677)
                ·
                  refine ⟨44257011718016973603629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118018697914711929609677 44257011718016973603629)
                  ·
                    refine ⟨16596379394256365101361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44257011718016973603629 16596379394256365101361)
                    ·
                      rfl

theorem cell22_48482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_48482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48482 prefixEnd_48482 := by exact prefixLift 48482
  have htrace : WordTrace (prefixWord ++ tailWord_48482) baseStart_48482 baseEnd_48482 := by
    simpa [prefixWord, tailWord_48482, baseEnd_48482] using wordTrace_append hprefix tailTrace_48482
  have hstable : (prefixWord ++ tailWord_48482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48482).length < 2 ^ (prefixWord ++ tailWord_48482).sum := by decide
  have hdescent : baseEnd_48482 < baseStart_48482 := by decide
  rcases family_descends (prefixWord ++ tailWord_48482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48495 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 5]
def baseStart_48495 : Nat := 118140960795 + 48495 * 2 ^ 59
def prefixEnd_48495 : Nat := 4983230072969 + 3 ^ 40 * 48495 * 2
def baseEnd_48495 : Nat := 5533609853309554842107

theorem tailTrace_48495 : CollatzResearch.WordTrace tailWord_48495 prefixEnd_48495 5533609853309554842107 := by
  unfold tailWord_48495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768757959318372131722939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179171972878914754481959 1768757959318372131722939)
  ·
    refine ⟨2653136938977558197584409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768757959318372131722939 2653136938977558197584409)
    ·
      refine ⟨1989852704233168648188307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2653136938977558197584409 1989852704233168648188307)
      ·
        refine ⟨2984779056349752972282461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989852704233168648188307 2984779056349752972282461)
        ·
          refine ⟨1119292146131157364605923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984779056349752972282461 1119292146131157364605923)
          ·
            refine ⟨1678938219196736046908885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119292146131157364605923 1678938219196736046908885)
            ·
              refine ⟨39350114512423501099427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1678938219196736046908885 39350114512423501099427)
              ·
                refine ⟨59025171768635251649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39350114512423501099427 59025171768635251649141)
                ·
                  refine ⟨5533609853309554842107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59025171768635251649141 5533609853309554842107)
                  ·
                    rfl

theorem cell22_48495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 5].length) (baseStart_48495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48495 prefixEnd_48495 := by exact prefixLift 48495
  have htrace : WordTrace (prefixWord ++ tailWord_48495) baseStart_48495 baseEnd_48495 := by
    simpa [prefixWord, tailWord_48495, baseEnd_48495] using wordTrace_append hprefix tailTrace_48495
  have hstable : (prefixWord ++ tailWord_48495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48495).length < 2 ^ (prefixWord ++ tailWord_48495).sum := by decide
  have hdescent : baseEnd_48495 < baseStart_48495 := by decide
  rcases family_descends (prefixWord ++ tailWord_48495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48568 : List Nat := [2, 1, 2, 1, 2, 2, 4, 8]
def baseStart_48568 : Nat := 118140960795 + 48568 * 2 ^ 59
def prefixEnd_48568 : Nat := 4983230072969 + 3 ^ 40 * 48568 * 2
def baseEnd_48568 : Nat := 1847313216864534161233

theorem tailTrace_48568 : CollatzResearch.WordTrace tailWord_48568 prefixEnd_48568 1847313216864534161233 := by
  unfold tailWord_48568
  simp only [CollatzResearch.WordTrace]
  refine ⟨885710244026952799565179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1180946992035937066086905 885710244026952799565179)
  ·
    refine ⟨1328565366040429199347769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 885710244026952799565179 1328565366040429199347769)
    ·
      refine ⟨996424024530321899510827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1328565366040429199347769 996424024530321899510827)
      ·
        refine ⟨1494636036795482849266241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996424024530321899510827 1494636036795482849266241)
        ·
          refine ⟨1120977027596612136949681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494636036795482849266241 1120977027596612136949681)
          ·
            refine ⟨840732770697459102712261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120977027596612136949681 840732770697459102712261)
            ·
              refine ⟨157637394505773581758549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840732770697459102712261 157637394505773581758549)
              ·
                refine ⟨1847313216864534161233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 157637394505773581758549 1847313216864534161233)
                ·
                  rfl

theorem cell22_48568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_48568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48568 prefixEnd_48568 := by exact prefixLift 48568
  have htrace : WordTrace (prefixWord ++ tailWord_48568) baseStart_48568 baseEnd_48568 := by
    simpa [prefixWord, tailWord_48568, baseEnd_48568] using wordTrace_append hprefix tailTrace_48568
  have hstable : (prefixWord ++ tailWord_48568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48568).length < 2 ^ (prefixWord ++ tailWord_48568).sum := by decide
  have hdescent : baseEnd_48568 < baseStart_48568 := by decide
  rcases family_descends (prefixWord ++ tailWord_48568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48572 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_48572 : Nat := 118140960795 + 48572 * 2 ^ 59
def prefixEnd_48572 : Nat := 4983230072969 + 3 ^ 40 * 48572 * 2
def baseEnd_48572 : Nat := 16627188233526130351085

theorem tailTrace_48572 : CollatzResearch.WordTrace tailWord_48572 prefixEnd_48572 16627188233526130351085 := by
  unfold tailWord_48572
  simp only [CollatzResearch.WordTrace]
  refine ⟨885783190019707141137985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1181044253359609521517313 885783190019707141137985)
  ·
    refine ⟨664337392514780355853489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 885783190019707141137985 664337392514780355853489)
    ·
      refine ⟨498253044386085266890117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 664337392514780355853489 498253044386085266890117)
      ·
        refine ⟨93422445822390987541897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498253044386085266890117 93422445822390987541897)
        ·
          refine ⟨70066834366793240656423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93422445822390987541897 70066834366793240656423)
          ·
            refine ⟨105100251550189860984635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70066834366793240656423 105100251550189860984635)
            ·
              refine ⟨157650377325284791476953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105100251550189860984635 157650377325284791476953)
              ·
                refine ⟨118237782993963593607715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157650377325284791476953 118237782993963593607715)
                ·
                  refine ⟨177356674490945390411573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118237782993963593607715 177356674490945390411573)
                  ·
                    refine ⟨16627188233526130351085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177356674490945390411573 16627188233526130351085)
                    ·
                      rfl

theorem cell22_48572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_48572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48572 prefixEnd_48572 := by exact prefixLift 48572
  have htrace : WordTrace (prefixWord ++ tailWord_48572) baseStart_48572 baseEnd_48572 := by
    simpa [prefixWord, tailWord_48572, baseEnd_48572] using wordTrace_append hprefix tailTrace_48572
  have hstable : (prefixWord ++ tailWord_48572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48572).length < 2 ^ (prefixWord ++ tailWord_48572).sum := by decide
  have hdescent : baseEnd_48572 < baseStart_48572 := by decide
  rcases family_descends (prefixWord ++ tailWord_48572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48621 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_48621 : Nat := 118140960795 + 48621 * 2 ^ 59
def prefixEnd_48621 : Nat := 4983230072969 + 3 ^ 40 * 48621 * 2
def baseEnd_48621 : Nat := 16643961934906335875935

theorem tailTrace_48621 : CollatzResearch.WordTrace tailWord_48621 prefixEnd_48621 16643961934906335875935 := by
  unfold tailWord_48621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773353556861895650809717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1182235704574597100539811 1773353556861895650809717)
  ·
    refine ⟨166251895955802717263411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1773353556861895650809717 166251895955802717263411)
    ·
      refine ⟨249377843933704075895117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166251895955802717263411 249377843933704075895117)
      ·
        refine ⟨93516691475139028460669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249377843933704075895117 93516691475139028460669)
        ·
          refine ⟨35068759303177135672751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93516691475139028460669 35068759303177135672751)
          ·
            refine ⟨52603138954765703509127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35068759303177135672751 52603138954765703509127)
            ·
              refine ⟨78904708432148555263691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52603138954765703509127 78904708432148555263691)
              ·
                refine ⟨118357062648222832895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78904708432148555263691 118357062648222832895537)
                ·
                  refine ⟨88767796986167124671653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118357062648222832895537 88767796986167124671653)
                  ·
                    refine ⟨16643961934906335875935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88767796986167124671653 16643961934906335875935)
                    ·
                      rfl

theorem cell22_48621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_48621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48621 prefixEnd_48621 := by exact prefixLift 48621
  have htrace : WordTrace (prefixWord ++ tailWord_48621) baseStart_48621 baseEnd_48621 := by
    simpa [prefixWord, tailWord_48621, baseEnd_48621] using wordTrace_append hprefix tailTrace_48621
  have hstable : (prefixWord ++ tailWord_48621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48621).length < 2 ^ (prefixWord ++ tailWord_48621).sum := by decide
  have hdescent : baseEnd_48621 < baseStart_48621 := by decide
  rcases family_descends (prefixWord ++ tailWord_48621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48634 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_48634 : Nat := 118140960795 + 48634 * 2 ^ 59
def prefixEnd_48634 : Nat := 4983230072969 + 3 ^ 40 * 48634 * 2
def baseEnd_48634 : Nat := 16648412100578635300895

theorem tailTrace_48634 : CollatzResearch.WordTrace tailWord_48634 prefixEnd_48634 16648412100578635300895 := by
  unfold tailWord_48634
  simp only [CollatzResearch.WordTrace]
  refine ⟨443456926453699717758239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1182551803876532580688637 443456926453699717758239)
  ·
    refine ⟨665185389680549576637359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 443456926453699717758239 665185389680549576637359)
    ·
      refine ⟨997778084520824364956039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665185389680549576637359 997778084520824364956039)
      ·
        refine ⟨1496667126781236547434059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997778084520824364956039 1496667126781236547434059)
        ·
          refine ⟨2245000690171854821151089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496667126781236547434059 2245000690171854821151089)
          ·
            refine ⟨1683750517628891115863317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2245000690171854821151089 1683750517628891115863317)
            ·
              refine ⟨78925805513854271056093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1683750517628891115863317 78925805513854271056093)
              ·
                refine ⟨29597177067695351646035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78925805513854271056093 29597177067695351646035)
                ·
                  refine ⟨44395765601543027469053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29597177067695351646035 44395765601543027469053)
                  ·
                    refine ⟨16648412100578635300895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44395765601543027469053 16648412100578635300895)
                    ·
                      rfl

theorem cell22_48634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_48634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48634 prefixEnd_48634 := by exact prefixLift 48634
  have htrace : WordTrace (prefixWord ++ tailWord_48634) baseStart_48634 baseEnd_48634 := by
    simpa [prefixWord, tailWord_48634, baseEnd_48634] using wordTrace_append hprefix tailTrace_48634
  have hstable : (prefixWord ++ tailWord_48634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48634).length < 2 ^ (prefixWord ++ tailWord_48634).sum := by decide
  have hdescent : baseEnd_48634 < baseStart_48634 := by decide
  rcases family_descends (prefixWord ++ tailWord_48634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48647 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 5]
def baseStart_48647 : Nat := 118140960795 + 48647 * 2 ^ 59
def prefixEnd_48647 : Nat := 4983230072969 + 3 ^ 40 * 48647 * 2
def baseEnd_48647 : Nat := 5550954088750311575285

theorem tailTrace_48647 : CollatzResearch.WordTrace tailWord_48647 prefixEnd_48647 5550954088750311575285 := by
  unfold tailWord_48647
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774301854767702091256195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1182867903178468060837463 1774301854767702091256195)
  ·
    refine ⟨2661452782151553136884293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1774301854767702091256195 2661452782151553136884293)
    ·
      refine ⟨499022396653416213165805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2661452782151553136884293 499022396653416213165805)
      ·
        refine ⟨187133398745031079937177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499022396653416213165805 187133398745031079937177)
        ·
          refine ⟨140350049058773309952883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187133398745031079937177 140350049058773309952883)
          ·
            refine ⟨210525073588159964929325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140350049058773309952883 210525073588159964929325)
            ·
              refine ⟨78946902595559986848497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210525073588159964929325 78946902595559986848497)
              ·
                refine ⟨59210176946669990136373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78946902595559986848497 59210176946669990136373)
                ·
                  refine ⟨5550954088750311575285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59210176946669990136373 5550954088750311575285)
                  ·
                    rfl

theorem cell22_48647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].length) (baseStart_48647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48647 prefixEnd_48647 := by exact prefixLift 48647
  have htrace : WordTrace (prefixWord ++ tailWord_48647) baseStart_48647 baseEnd_48647 := by
    simpa [prefixWord, tailWord_48647, baseEnd_48647] using wordTrace_append hprefix tailTrace_48647
  have hstable : (prefixWord ++ tailWord_48647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48647).length < 2 ^ (prefixWord ++ tailWord_48647).sum := by decide
  have hdescent : baseEnd_48647 < baseStart_48647 := by decide
  rcases family_descends (prefixWord ++ tailWord_48647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48664 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_48664 : Nat := 118140960795 + 48664 * 2 ^ 59
def prefixEnd_48664 : Nat := 4983230072969 + 3 ^ 40 * 48664 * 2
def baseEnd_48664 : Nat := 5552893904556185683601

theorem tailTrace_48664 : CollatzResearch.WordTrace tailWord_48664 prefixEnd_48664 5552893904556185683601 := by
  unfold tailWord_48664
  simp only [CollatzResearch.WordTrace]
  refine ⟨887460947853056997312523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1183281263804075996416697 887460947853056997312523)
  ·
    refine ⟨1331191421779585495968785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887460947853056997312523 1331191421779585495968785)
    ·
      refine ⟨998393566334689121976589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331191421779585495968785 998393566334689121976589)
      ·
        refine ⟨374397587375508420741221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 998393566334689121976589 374397587375508420741221)
        ·
          refine ⟨70199547632907828888979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374397587375508420741221 70199547632907828888979)
          ·
            refine ⟨105299321449361743333469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70199547632907828888979 105299321449361743333469)
            ·
              refine ⟨39487245543510653750051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105299321449361743333469 39487245543510653750051)
              ·
                refine ⟨59230868315265980625077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39487245543510653750051 59230868315265980625077)
                ·
                  refine ⟨5552893904556185683601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59230868315265980625077 5552893904556185683601)
                  ·
                    rfl

theorem cell22_48664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_48664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48664 prefixEnd_48664 := by exact prefixLift 48664
  have htrace : WordTrace (prefixWord ++ tailWord_48664) baseStart_48664 baseEnd_48664 := by
    simpa [prefixWord, tailWord_48664, baseEnd_48664] using wordTrace_append hprefix tailTrace_48664
  have hstable : (prefixWord ++ tailWord_48664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48664).length < 2 ^ (prefixWord ++ tailWord_48664).sum := by decide
  have hdescent : baseEnd_48664 < baseStart_48664 := by decide
  rcases family_descends (prefixWord ++ tailWord_48664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48670 : List Nat := [4, 3, 3, 1, 2, 1, 2, 6]
def baseStart_48670 : Nat := 118140960795 + 48670 * 2 ^ 59
def prefixEnd_48670 : Nat := 4983230072969 + 3 ^ 40 * 48670 * 2
def baseEnd_48670 : Nat := 1851192848476282377865

theorem tailTrace_48670 : CollatzResearch.WordTrace tailWord_48670 prefixEnd_48670 1851192848476282377865 := by
  unfold tailWord_48670
  simp only [CollatzResearch.WordTrace]
  refine ⟨221892591710547127417933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1183427155789584679562309 221892591710547127417933)
  ·
    refine ⟨83209721891455172781725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221892591710547127417933 83209721891455172781725)
    ·
      refine ⟨31203645709295689793147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83209721891455172781725 31203645709295689793147)
      ·
        refine ⟨46805468563943534689721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31203645709295689793147 46805468563943534689721)
        ·
          refine ⟨35104101422957651017291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46805468563943534689721 35104101422957651017291)
          ·
            refine ⟨52656152134436476525937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35104101422957651017291 52656152134436476525937)
            ·
              refine ⟨39492114100827357394453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52656152134436476525937 39492114100827357394453)
              ·
                refine ⟨1851192848476282377865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39492114100827357394453 1851192848476282377865)
                ·
                  rfl

theorem cell22_48670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_48670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48670 prefixEnd_48670 := by exact prefixLift 48670
  have htrace : WordTrace (prefixWord ++ tailWord_48670) baseStart_48670 baseEnd_48670 := by
    simpa [prefixWord, tailWord_48670, baseEnd_48670] using wordTrace_append hprefix tailTrace_48670
  have hstable : (prefixWord ++ tailWord_48670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48670).length < 2 ^ (prefixWord ++ tailWord_48670).sum := by decide
  have hdescent : baseEnd_48670 < baseStart_48670 := by decide
  rcases family_descends (prefixWord ++ tailWord_48670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48690 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_48690 : Nat := 118140960795 + 48690 * 2 ^ 59
def prefixEnd_48690 : Nat := 4983230072969 + 3 ^ 40 * 48690 * 2
def baseEnd_48690 : Nat := 16667582045013155900723

theorem tailTrace_48690 : CollatzResearch.WordTrace tailWord_48690 prefixEnd_48690 16667582045013155900723 := by
  unfold tailWord_48690
  simp only [CollatzResearch.WordTrace]
  refine ⟨443967548402980108767881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1183913462407946956714349 443967548402980108767881)
  ·
    refine ⟨332975661302235081575911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 443967548402980108767881 332975661302235081575911)
    ·
      refine ⟨499463491953352622363867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332975661302235081575911 499463491953352622363867)
      ·
        refine ⟨749195237930028933545801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499463491953352622363867 749195237930028933545801)
        ·
          refine ⟨561896428447521700159351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749195237930028933545801 561896428447521700159351)
          ·
            refine ⟨842844642671282550239027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561896428447521700159351 842844642671282550239027)
            ·
              refine ⟨1264266964006923825358541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842844642671282550239027 1264266964006923825358541)
              ·
                refine ⟨474100111502596434509453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1264266964006923825358541 474100111502596434509453)
                ·
                  refine ⟨177787541813473662941045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474100111502596434509453 177787541813473662941045)
                  ·
                    refine ⟨16667582045013155900723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177787541813473662941045 16667582045013155900723)
                    ·
                      rfl

theorem cell22_48690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_48690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48690 prefixEnd_48690 := by exact prefixLift 48690
  have htrace : WordTrace (prefixWord ++ tailWord_48690) baseStart_48690 baseEnd_48690 := by
    simpa [prefixWord, tailWord_48690, baseEnd_48690] using wordTrace_append hprefix tailTrace_48690
  have hstable : (prefixWord ++ tailWord_48690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48690).length < 2 ^ (prefixWord ++ tailWord_48690).sum := by decide
  have hdescent : baseEnd_48690 < baseStart_48690 := by decide
  rcases family_descends (prefixWord ++ tailWord_48690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48709 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 4]
def baseStart_48709 : Nat := 118140960795 + 48709 * 2 ^ 59
def prefixEnd_48709 : Nat := 4983230072969 + 3 ^ 40 * 48709 * 2
def baseEnd_48709 : Nat := 5558028711101146558555

theorem tailTrace_48709 : CollatzResearch.WordTrace tailWord_48709 prefixEnd_48709 5558028711101146558555 := by
  unfold tailWord_48709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776563180543086680013181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1184375453695391120008787 1776563180543086680013181)
  ·
    refine ⟨666211192703657505004943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1776563180543086680013181 666211192703657505004943)
    ·
      refine ⟨999316789055486257507415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666211192703657505004943 999316789055486257507415)
      ·
        refine ⟨1498975183583229386261123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999316789055486257507415 1498975183583229386261123)
        ·
          refine ⟨2248462775374844079391685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498975183583229386261123 2248462775374844079391685)
          ·
            refine ⟨421586770382783264885941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2248462775374844079391685 421586770382783264885941)
            ·
              refine ⟨39523759723385931083057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 421586770382783264885941 39523759723385931083057)
              ·
                refine ⟨29642819792539448312293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39523759723385931083057 29642819792539448312293)
                ·
                  refine ⟨5558028711101146558555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29642819792539448312293 5558028711101146558555)
                  ·
                    rfl

theorem cell22_48709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_48709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48709 prefixEnd_48709 := by exact prefixLift 48709
  have htrace : WordTrace (prefixWord ++ tailWord_48709) baseStart_48709 baseEnd_48709 := by
    simpa [prefixWord, tailWord_48709, baseEnd_48709] using wordTrace_append hprefix tailTrace_48709
  have hstable : (prefixWord ++ tailWord_48709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48709).length < 2 ^ (prefixWord ++ tailWord_48709).sum := by decide
  have hdescent : baseEnd_48709 < baseStart_48709 := by decide
  rcases family_descends (prefixWord ++ tailWord_48709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48720 : List Nat := [2, 1, 1, 1, 1, 3, 6, 7]
def baseStart_48720 : Nat := 118140960795 + 48720 * 2 ^ 59
def prefixEnd_48720 : Nat := 4983230072969 + 3 ^ 40 * 48720 * 2
def baseEnd_48720 : Nat := 1853094628678119738959

theorem tailTrace_48720 : CollatzResearch.WordTrace tailWord_48720 prefixEnd_48720 1853094628678119738959 := by
  unfold tailWord_48720
  simp only [CollatzResearch.WordTrace]
  refine ⟨888482191751617779331807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1184642922335490372442409 888482191751617779331807)
  ·
    refine ⟨1332723287627426668997711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 888482191751617779331807 1332723287627426668997711)
    ·
      refine ⟨1999084931441140003496567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332723287627426668997711 1999084931441140003496567)
      ·
        refine ⟨2998627397161710005244851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999084931441140003496567 2998627397161710005244851)
        ·
          refine ⟨4497941095742565007867277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998627397161710005244851 4497941095742565007867277)
          ·
            refine ⟨1686727910903461877950229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4497941095742565007867277 1686727910903461877950229)
            ·
              refine ⟨79065370823599775528917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1686727910903461877950229 79065370823599775528917)
              ·
                refine ⟨1853094628678119738959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79065370823599775528917 1853094628678119738959)
                ·
                  rfl

theorem cell22_48720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 7].length) (baseStart_48720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48720 prefixEnd_48720 := by exact prefixLift 48720
  have htrace : WordTrace (prefixWord ++ tailWord_48720) baseStart_48720 baseEnd_48720 := by
    simpa [prefixWord, tailWord_48720, baseEnd_48720] using wordTrace_append hprefix tailTrace_48720
  have hstable : (prefixWord ++ tailWord_48720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48720).length < 2 ^ (prefixWord ++ tailWord_48720).sum := by decide
  have hdescent : baseEnd_48720 < baseStart_48720 := by decide
  rcases family_descends (prefixWord ++ tailWord_48720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48724 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_48724 : Nat := 118140960795 + 48724 * 2 ^ 59
def prefixEnd_48724 : Nat := 4983230072969 + 3 ^ 40 * 48724 * 2
def baseEnd_48724 : Nat := 16679220939848400550619

theorem tailTrace_48724 : CollatzResearch.WordTrace tailWord_48724 prefixEnd_48724 16679220939848400550619 := by
  unfold tailWord_48724
  simp only [CollatzResearch.WordTrace]
  refine ⟨888555137744372120904613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1184740183659162827872817 888555137744372120904613)
  ·
    refine ⟨166604088327069772669615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 888555137744372120904613 166604088327069772669615)
    ·
      refine ⟨249906132490604659004423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166604088327069772669615 249906132490604659004423)
      ·
        refine ⟨374859198735906988506635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249906132490604659004423 374859198735906988506635)
        ·
          refine ⟨562288798103860482759953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374859198735906988506635 562288798103860482759953)
          ·
            refine ⟨421716598577895362069965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562288798103860482759953 421716598577895362069965)
            ·
              refine ⟨158143724466710760776237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421716598577895362069965 158143724466710760776237)
              ·
                refine ⟨59303896675016535291089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158143724466710760776237 59303896675016535291089)
                ·
                  refine ⟨44477922506262401468317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59303896675016535291089 44477922506262401468317)
                  ·
                    refine ⟨16679220939848400550619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44477922506262401468317 16679220939848400550619)
                    ·
                      rfl

theorem cell22_48724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_48724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48724 prefixEnd_48724 := by exact prefixLift 48724
  have htrace : WordTrace (prefixWord ++ tailWord_48724) baseStart_48724 baseEnd_48724 := by
    simpa [prefixWord, tailWord_48724, baseEnd_48724] using wordTrace_append hprefix tailTrace_48724
  have hstable : (prefixWord ++ tailWord_48724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48724).length < 2 ^ (prefixWord ++ tailWord_48724).sum := by decide
  have hdescent : baseEnd_48724 < baseStart_48724 := by decide
  rcases family_descends (prefixWord ++ tailWord_48724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48786 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_48786 : Nat := 118140960795 + 48786 * 2 ^ 59
def prefixEnd_48786 : Nat := 4983230072969 + 3 ^ 40 * 48786 * 2
def baseEnd_48786 : Nat := 16700444806900905500429

theorem tailTrace_48786 : CollatzResearch.WordTrace tailWord_48786 prefixEnd_48786 16700444806900905500429 := by
  unfold tailWord_48786
  simp only [CollatzResearch.WordTrace]
  refine ⟨444842900316032207641553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1186247734176085887044141 444842900316032207641553)
  ·
    refine ⟨333632175237024155731165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 444842900316032207641553 333632175237024155731165)
    ·
      refine ⟨125112065713884058399187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333632175237024155731165 125112065713884058399187)
      ·
        refine ⟨187668098570826087598781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125112065713884058399187 187668098570826087598781)
        ·
          refine ⟨70375536964059782849543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187668098570826087598781 70375536964059782849543)
          ·
            refine ⟨105563305446089674274315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70375536964059782849543 105563305446089674274315)
            ·
              refine ⟨158344958169134511411473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105563305446089674274315 158344958169134511411473)
              ·
                refine ⟨118758718626850883558605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158344958169134511411473 118758718626850883558605)
                ·
                  refine ⟨44534519485069081334477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118758718626850883558605 44534519485069081334477)
                  ·
                    refine ⟨16700444806900905500429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44534519485069081334477 16700444806900905500429)
                    ·
                      rfl

theorem cell22_48786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_48786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48786 prefixEnd_48786 := by exact prefixLift 48786
  have htrace : WordTrace (prefixWord ++ tailWord_48786) baseStart_48786 baseEnd_48786 := by
    simpa [prefixWord, tailWord_48786, baseEnd_48786] using wordTrace_append hprefix tailTrace_48786
  have hstable : (prefixWord ++ tailWord_48786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48786).length < 2 ^ (prefixWord ++ tailWord_48786).sum := by decide
  have hdescent : baseEnd_48786 < baseStart_48786 := by decide
  rcases family_descends (prefixWord ++ tailWord_48786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48854 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_48854 : Nat := 118140960795 + 48854 * 2 ^ 59
def prefixEnd_48854 : Nat := 4983230072969 + 3 ^ 40 * 48854 * 2
def baseEnd_48854 : Nat := 16723722596571394800221

theorem tailTrace_48854 : CollatzResearch.WordTrace tailWord_48854 prefixEnd_48854 16723722596571394800221 := by
  unfold tailWord_48854
  simp only [CollatzResearch.WordTrace]
  refine ⟨111365735313611027752601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1187901176678517629361077 111365735313611027752601)
  ·
    refine ⟨83524301485208270814451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111365735313611027752601 83524301485208270814451)
    ·
      refine ⟨125286452227812406221677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83524301485208270814451 125286452227812406221677)
      ·
        refine ⟨46982419585429652333129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125286452227812406221677 46982419585429652333129)
        ·
          refine ⟨35236814689072239249847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46982419585429652333129 35236814689072239249847)
          ·
            refine ⟨52855222033608358874771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35236814689072239249847 52855222033608358874771)
            ·
              refine ⟨79282833050412538312157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52855222033608358874771 79282833050412538312157)
              ·
                refine ⟨29731062393904701867059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79282833050412538312157 29731062393904701867059)
                ·
                  refine ⟨44596593590857052800589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29731062393904701867059 44596593590857052800589)
                  ·
                    refine ⟨16723722596571394800221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44596593590857052800589 16723722596571394800221)
                    ·
                      rfl

theorem cell22_48854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_48854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48854 prefixEnd_48854 := by exact prefixLift 48854
  have htrace : WordTrace (prefixWord ++ tailWord_48854) baseStart_48854 baseEnd_48854 := by
    simpa [prefixWord, tailWord_48854, baseEnd_48854] using wordTrace_append hprefix tailTrace_48854
  have hstable : (prefixWord ++ tailWord_48854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48854).length < 2 ^ (prefixWord ++ tailWord_48854).sum := by decide
  have hdescent : baseEnd_48854 < baseStart_48854 := by decide
  rcases family_descends (prefixWord ++ tailWord_48854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48857 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_48857 : Nat := 118140960795 + 48857 * 2 ^ 59
def prefixEnd_48857 : Nat := 4983230072969 + 3 ^ 40 * 48857 * 2
def baseEnd_48857 : Nat := 16724749557880386975211

theorem tailTrace_48857 : CollatzResearch.WordTrace tailWord_48857 prefixEnd_48857 16724749557880386975211 := by
  unfold tailWord_48857
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781961184006907956400825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1187974122671271970933883 1781961184006907956400825)
  ·
    refine ⟨1336470888005180967300619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1781961184006907956400825 1336470888005180967300619)
    ·
      refine ⟨2004706332007771450950929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336470888005180967300619 2004706332007771450950929)
      ·
        refine ⟨1503529749005828588213197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004706332007771450950929 1503529749005828588213197)
        ·
          refine ⟨563823655877185720579949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1503529749005828588213197 563823655877185720579949)
          ·
            refine ⟨211433870953944645217481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563823655877185720579949 211433870953944645217481)
            ·
              refine ⟨158575403215458483913111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211433870953944645217481 158575403215458483913111)
              ·
                refine ⟨237863104823187725869667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158575403215458483913111 237863104823187725869667)
                ·
                  refine ⟨356794657234781588804501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237863104823187725869667 356794657234781588804501)
                  ·
                    refine ⟨16724749557880386975211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 356794657234781588804501 16724749557880386975211)
                    ·
                      rfl

theorem cell22_48857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_48857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48857 prefixEnd_48857 := by exact prefixLift 48857
  have htrace : WordTrace (prefixWord ++ tailWord_48857) baseStart_48857 baseEnd_48857 := by
    simpa [prefixWord, tailWord_48857, baseEnd_48857] using wordTrace_append hprefix tailTrace_48857
  have hstable : (prefixWord ++ tailWord_48857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48857).length < 2 ^ (prefixWord ++ tailWord_48857).sum := by decide
  have hdescent : baseEnd_48857 < baseStart_48857 := by decide
  rcases family_descends (prefixWord ++ tailWord_48857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48872 : List Nat := [2, 1, 4, 1, 3, 1, 10]
def baseStart_48872 : Nat := 118140960795 + 48872 * 2 ^ 59
def prefixEnd_48872 : Nat := 4983230072969 + 3 ^ 40 * 48872 * 2
def baseEnd_48872 : Nat := 619625346830568438895

theorem tailTrace_48872 : CollatzResearch.WordTrace tailWord_48872 prefixEnd_48872 619625346830568438895 := by
  unfold tailWord_48872
  simp only [CollatzResearch.WordTrace]
  refine ⟨891254139476282759098435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1188338852635043678797913 891254139476282759098435)
  ·
    refine ⟨1336881209214424138647653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891254139476282759098435 1336881209214424138647653)
    ·
      refine ⟨250665226727704525996435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1336881209214424138647653 250665226727704525996435)
      ·
        refine ⟨375997840091556788994653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250665226727704525996435 375997840091556788994653)
        ·
          refine ⟨140999190034333795872995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375997840091556788994653 140999190034333795872995)
          ·
            refine ⟨211498785051500693809493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140999190034333795872995 211498785051500693809493)
            ·
              refine ⟨619625346830568438895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 211498785051500693809493 619625346830568438895)
              ·
                rfl

theorem cell22_48872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 10].length) (baseStart_48872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48872 prefixEnd_48872 := by exact prefixLift 48872
  have htrace : WordTrace (prefixWord ++ tailWord_48872) baseStart_48872 baseEnd_48872 := by
    simpa [prefixWord, tailWord_48872, baseEnd_48872] using wordTrace_append hprefix tailTrace_48872
  have hstable : (prefixWord ++ tailWord_48872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48872).length < 2 ^ (prefixWord ++ tailWord_48872).sum := by decide
  have hdescent : baseEnd_48872 < baseStart_48872 := by decide
  rcases family_descends (prefixWord ++ tailWord_48872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48904 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_48904 : Nat := 118140960795 + 48904 * 2 ^ 59
def prefixEnd_48904 : Nat := 4983230072969 + 3 ^ 40 * 48904 * 2
def baseEnd_48904 : Nat := 16740838618387931050067

theorem tailTrace_48904 : CollatzResearch.WordTrace tailWord_48904 prefixEnd_48904 16740838618387931050067 := by
  unfold tailWord_48904
  simp only [CollatzResearch.WordTrace]
  refine ⟨891837707418317491680883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1189116943224423322241177 891837707418317491680883)
  ·
    refine ⟨1337756561127476237521325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891837707418317491680883 1337756561127476237521325)
    ·
      refine ⟨501658710422803589070497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1337756561127476237521325 501658710422803589070497)
      ·
        refine ⟨376244032817102691802873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501658710422803589070497 376244032817102691802873)
        ·
          refine ⟨282183024612827018852155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376244032817102691802873 282183024612827018852155)
          ·
            refine ⟨423274536919240528278233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282183024612827018852155 423274536919240528278233)
            ·
              refine ⟨317455902689430396208675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423274536919240528278233 317455902689430396208675)
              ·
                refine ⟨476183854034145594313013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317455902689430396208675 476183854034145594313013)
                ·
                  refine ⟨44642236315701149466845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 476183854034145594313013 44642236315701149466845)
                  ·
                    refine ⟨16740838618387931050067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44642236315701149466845 16740838618387931050067)
                    ·
                      rfl

theorem cell22_48904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_48904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48904 prefixEnd_48904 := by exact prefixLift 48904
  have htrace : WordTrace (prefixWord ++ tailWord_48904) baseStart_48904 baseEnd_48904 := by
    simpa [prefixWord, tailWord_48904, baseEnd_48904] using wordTrace_append hprefix tailTrace_48904
  have hstable : (prefixWord ++ tailWord_48904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48904).length < 2 ^ (prefixWord ++ tailWord_48904).sum := by decide
  have hdescent : baseEnd_48904 < baseStart_48904 := by decide
  rcases family_descends (prefixWord ++ tailWord_48904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48981 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_48981 : Nat := 118140960795 + 48981 * 2 ^ 59
def prefixEnd_48981 : Nat := 4983230072969 + 3 ^ 40 * 48981 * 2
def baseEnd_48981 : Nat := 16767197291985396874831

theorem tailTrace_48981 : CollatzResearch.WordTrace tailWord_48981 prefixEnd_48981 16767197291985396874831 := by
  unfold tailWord_48981
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786483835557677133914797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1190989223705118089276531 1786483835557677133914797)
  ·
    refine ⟨669931438334128925218049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1786483835557677133914797 669931438334128925218049)
    ·
      refine ⟨502448578750596693913537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 669931438334128925218049 502448578750596693913537)
      ·
        refine ⟨376836434062947520435153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502448578750596693913537 376836434062947520435153)
        ·
          refine ⟨282627325547210640326365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376836434062947520435153 282627325547210640326365)
          ·
            refine ⟨105985247080203990122387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282627325547210640326365 105985247080203990122387)
            ·
              refine ⟨158977870620305985183581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105985247080203990122387 158977870620305985183581)
              ·
                refine ⟨59616701482614744443843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158977870620305985183581 59616701482614744443843)
                ·
                  refine ⟨89425052223922116665765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59616701482614744443843 89425052223922116665765)
                  ·
                    refine ⟨16767197291985396874831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89425052223922116665765 16767197291985396874831)
                    ·
                      rfl

theorem cell22_48981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_48981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48981 prefixEnd_48981 := by exact prefixLift 48981
  have htrace : WordTrace (prefixWord ++ tailWord_48981) baseStart_48981 baseEnd_48981 := by
    simpa [prefixWord, tailWord_48981, baseEnd_48981] using wordTrace_append hprefix tailTrace_48981
  have hstable : (prefixWord ++ tailWord_48981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48981).length < 2 ^ (prefixWord ++ tailWord_48981).sum := by decide
  have hdescent : baseEnd_48981 < baseStart_48981 := by decide
  rcases family_descends (prefixWord ++ tailWord_48981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48996 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 6]
def baseStart_48996 : Nat := 118140960795 + 48996 * 2 ^ 59
def prefixEnd_48996 : Nat := 4983230072969 + 3 ^ 40 * 48996 * 2
def baseEnd_48996 : Nat := 5590777366176785916595

theorem tailTrace_48996 : CollatzResearch.WordTrace tailWord_48996 prefixEnd_48996 5590777366176785916595 := by
  unfold tailWord_48996
  simp only [CollatzResearch.WordTrace]
  refine ⟨893515465251667347855421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1191353953668889797140561 893515465251667347855421)
  ·
    refine ⟨335068299469375255445783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 893515465251667347855421 335068299469375255445783)
    ·
      refine ⟨502602449204062883168675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335068299469375255445783 502602449204062883168675)
      ·
        refine ⟨753903673806094324753013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502602449204062883168675 753903673806094324753013)
        ·
          refine ⟨70678469419321342945595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 753903673806094324753013 70678469419321342945595)
          ·
            refine ⟨106017704128982014418393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70678469419321342945595 106017704128982014418393)
            ·
              refine ⟨79513278096736510813795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106017704128982014418393 79513278096736510813795)
              ·
                refine ⟨119269917145104766220693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79513278096736510813795 119269917145104766220693)
                ·
                  refine ⟨5590777366176785916595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119269917145104766220693 5590777366176785916595)
                  ·
                    rfl

theorem cell22_48996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_48996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_48996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_48996 prefixEnd_48996 := by exact prefixLift 48996
  have htrace : WordTrace (prefixWord ++ tailWord_48996) baseStart_48996 baseEnd_48996 := by
    simpa [prefixWord, tailWord_48996, baseEnd_48996] using wordTrace_append hprefix tailTrace_48996
  have hstable : (prefixWord ++ tailWord_48996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48996).length < 2 ^ (prefixWord ++ tailWord_48996).sum := by decide
  have hdescent : baseEnd_48996 < baseStart_48996 := by decide
  rcases family_descends (prefixWord ++ tailWord_48996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49148 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_49148 : Nat := 118140960795 + 49148 * 2 ^ 59
def prefixEnd_49148 : Nat := 4983230072969 + 3 ^ 40 * 49148 * 2
def baseEnd_49148 : Nat := 5608121601617542649773

theorem tailTrace_49148 : CollatzResearch.WordTrace tailWord_49148 prefixEnd_49148 5608121601617542649773 := by
  unfold tailWord_49148
  simp only [CollatzResearch.WordTrace]
  refine ⟨896287412976332327622049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1195049883968443103496065 896287412976332327622049)
  ·
    refine ⟨672215559732249245716537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 896287412976332327622049 672215559732249245716537)
    ·
      refine ⟨504161669799186934287403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 672215559732249245716537 504161669799186934287403)
      ·
        refine ⟨756242504698780401431105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504161669799186934287403 756242504698780401431105)
        ·
          refine ⟨567181878524085301073329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756242504698780401431105 567181878524085301073329)
          ·
            refine ⟨425386408893063975804997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567181878524085301073329 425386408893063975804997)
            ·
              refine ⟨79759951667449495463437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425386408893063975804997 79759951667449495463437)
              ·
                refine ⟨29909981875293560798789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79759951667449495463437 29909981875293560798789)
                ·
                  refine ⟨5608121601617542649773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29909981875293560798789 5608121601617542649773)
                  ·
                    rfl

theorem cell22_49148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_49148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49148 prefixEnd_49148 := by exact prefixLift 49148
  have htrace : WordTrace (prefixWord ++ tailWord_49148) baseStart_49148 baseEnd_49148 := by
    simpa [prefixWord, tailWord_49148, baseEnd_49148] using wordTrace_append hprefix tailTrace_49148
  have hstable : (prefixWord ++ tailWord_49148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49148).length < 2 ^ (prefixWord ++ tailWord_49148).sum := by decide
  have hdescent : baseEnd_49148 < baseStart_49148 := by decide
  rcases family_descends (prefixWord ++ tailWord_49148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49150 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_49150 : Nat := 118140960795 + 49150 * 2 ^ 59
def prefixEnd_49150 : Nat := 4983230072969 + 3 ^ 40 * 49150 * 2
def baseEnd_49150 : Nat := 16825049445725289399313

theorem tailTrace_49150 : CollatzResearch.WordTrace tailWord_49150 prefixEnd_49150 16825049445725289399313 := by
  unfold tailWord_49150
  simp only [CollatzResearch.WordTrace]
  refine ⟨224080971493177374602113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1195098514630279331211269 224080971493177374602113)
  ·
    refine ⟨168060728619883030951585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224080971493177374602113 168060728619883030951585)
    ·
      refine ⟨126045546464912273213689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168060728619883030951585 126045546464912273213689)
      ·
        refine ⟨94534159848684204910267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126045546464912273213689 94534159848684204910267)
        ·
          refine ⟨141801239773026307365401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94534159848684204910267 141801239773026307365401)
          ·
            refine ⟨106350929829769730524051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141801239773026307365401 106350929829769730524051)
            ·
              refine ⟨159526394744654595786077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106350929829769730524051 159526394744654595786077)
              ·
                refine ⟨59822398029245473419779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159526394744654595786077 59822398029245473419779)
                ·
                  refine ⟨89733597043868210129669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59822398029245473419779 89733597043868210129669)
                  ·
                    refine ⟨16825049445725289399313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89733597043868210129669 16825049445725289399313)
                    ·
                      rfl

theorem cell22_49150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_49150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49150 prefixEnd_49150 := by exact prefixLift 49150
  have htrace : WordTrace (prefixWord ++ tailWord_49150) baseStart_49150 baseEnd_49150 := by
    simpa [prefixWord, tailWord_49150, baseEnd_49150] using wordTrace_append hprefix tailTrace_49150
  have hstable : (prefixWord ++ tailWord_49150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49150).length < 2 ^ (prefixWord ++ tailWord_49150).sum := by decide
  have hdescent : baseEnd_49150 < baseStart_49150 := by decide
  rcases family_descends (prefixWord ++ tailWord_49150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49221 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 5]
def baseStart_49221 : Nat := 118140960795 + 49221 * 2 ^ 59
def prefixEnd_49221 : Nat := 4983230072969 + 3 ^ 40 * 49221 * 2
def baseEnd_49221 : Nat := 5616451398901590291365

theorem tailTrace_49221 : CollatzResearch.WordTrace tailWord_49221 prefixEnd_49221 5616451398901590291365 := by
  unfold tailWord_49221
  simp only [CollatzResearch.WordTrace]
  refine ⟨1795237354688198122651517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1196824903125465415101011 1795237354688198122651517)
  ·
    refine ⟨673214008008074295994319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1795237354688198122651517 673214008008074295994319)
    ·
      refine ⟨1009821012012111443991479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673214008008074295994319 1009821012012111443991479)
      ·
        refine ⟨1514731518018167165987219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009821012012111443991479 1514731518018167165987219)
        ·
          refine ⟨2272097277027250748980829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514731518018167165987219 2272097277027250748980829)
          ·
            refine ⟨852036478885219030867811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2272097277027250748980829 852036478885219030867811)
            ·
              refine ⟨1278054718327828546301717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852036478885219030867811 1278054718327828546301717)
              ·
                refine ⟨59908814921616963107893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1278054718327828546301717 59908814921616963107893)
                ·
                  refine ⟨5616451398901590291365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59908814921616963107893 5616451398901590291365)
                  ·
                    rfl

theorem cell22_49221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_49221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49221 prefixEnd_49221 := by exact prefixLift 49221
  have htrace : WordTrace (prefixWord ++ tailWord_49221) baseStart_49221 baseEnd_49221 := by
    simpa [prefixWord, tailWord_49221, baseEnd_49221] using wordTrace_append hprefix tailTrace_49221
  have hstable : (prefixWord ++ tailWord_49221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49221).length < 2 ^ (prefixWord ++ tailWord_49221).sum := by decide
  have hdescent : baseEnd_49221 < baseStart_49221 := by decide
  rcases family_descends (prefixWord ++ tailWord_49221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_49236 : Nat := 118140960795 + 49236 * 2 ^ 59
def prefixEnd_49236 : Nat := 4983230072969 + 3 ^ 40 * 49236 * 2
def baseEnd_49236 : Nat := 16854489003249731749049

theorem tailTrace_49236 : CollatzResearch.WordTrace tailWord_49236 prefixEnd_49236 16854489003249731749049 := by
  unfold tailWord_49236
  simp only [CollatzResearch.WordTrace]
  refine ⟨897892224816927842223781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1197189633089237122965041 897892224816927842223781)
  ·
    refine ⟨168354792153173970416959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 897892224816927842223781 168354792153173970416959)
    ·
      refine ⟨252532188229760955625439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168354792153173970416959 252532188229760955625439)
      ·
        refine ⟨378798282344641433438159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252532188229760955625439 378798282344641433438159)
        ·
          refine ⟨568197423516962150157239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378798282344641433438159 568197423516962150157239)
          ·
            refine ⟨852296135275443225235859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568197423516962150157239 852296135275443225235859)
            ·
              refine ⟨1278444202913164837853789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852296135275443225235859 1278444202913164837853789)
              ·
                refine ⟨479416576092436814195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278444202913164837853789 479416576092436814195171)
                ·
                  refine ⟨719124864138655221292757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479416576092436814195171 719124864138655221292757)
                  ·
                    refine ⟨16854489003249731749049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 719124864138655221292757 16854489003249731749049)
                    ·
                      rfl

theorem cell22_49236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_49236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49236 prefixEnd_49236 := by exact prefixLift 49236
  have htrace : WordTrace (prefixWord ++ tailWord_49236) baseStart_49236 baseEnd_49236 := by
    simpa [prefixWord, tailWord_49236, baseEnd_49236] using wordTrace_append hprefix tailTrace_49236
  have hstable : (prefixWord ++ tailWord_49236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49236).length < 2 ^ (prefixWord ++ tailWord_49236).sum := by decide
  have hdescent : baseEnd_49236 < baseStart_49236 := by decide
  rcases family_descends (prefixWord ++ tailWord_49236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49296 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_49296 : Nat := 118140960795 + 49296 * 2 ^ 59
def prefixEnd_49296 : Nat := 4983230072969 + 3 ^ 40 * 49296 * 2
def baseEnd_49296 : Nat := 16875028229429575248865

theorem tailTrace_49296 : CollatzResearch.WordTrace tailWord_49296 prefixEnd_49296 16875028229429575248865 := by
  unfold tailWord_49296
  simp only [CollatzResearch.WordTrace]
  refine ⟨898986414708242965815871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1198648552944323954421161 898986414708242965815871)
  ·
    refine ⟨1348479622062364448723807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 898986414708242965815871 1348479622062364448723807)
    ·
      refine ⟨2022719433093546673085711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348479622062364448723807 2022719433093546673085711)
      ·
        refine ⟨3034079149640320009628567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2022719433093546673085711 3034079149640320009628567)
        ·
          refine ⟨4551118724460480014442851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034079149640320009628567 4551118724460480014442851)
          ·
            refine ⟨6826678086690720021664277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551118724460480014442851 6826678086690720021664277)
            ·
              refine ⟨320000535313627501015513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6826678086690720021664277 320000535313627501015513)
              ·
                refine ⟨240000401485220625761635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320000535313627501015513 240000401485220625761635)
                ·
                  refine ⟨360000602227830938642453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240000401485220625761635 360000602227830938642453)
                  ·
                    refine ⟨16875028229429575248865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360000602227830938642453 16875028229429575248865)
                    ·
                      rfl

theorem cell22_49296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_49296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49296 prefixEnd_49296 := by exact prefixLift 49296
  have htrace : WordTrace (prefixWord ++ tailWord_49296) baseStart_49296 baseEnd_49296 := by
    simpa [prefixWord, tailWord_49296, baseEnd_49296] using wordTrace_append hprefix tailTrace_49296
  have hstable : (prefixWord ++ tailWord_49296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49296).length < 2 ^ (prefixWord ++ tailWord_49296).sum := by decide
  have hdescent : baseEnd_49296 < baseStart_49296 := by decide
  rcases family_descends (prefixWord ++ tailWord_49296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49313 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_49313 : Nat := 118140960795 + 49313 * 2 ^ 59
def prefixEnd_49313 : Nat := 4983230072969 + 3 ^ 40 * 49313 * 2
def baseEnd_49313 : Nat := 16880847676847197573813

theorem tailTrace_49313 : CollatzResearch.WordTrace tailWord_49313 prefixEnd_49313 16880847676847197573813 := by
  unfold tailWord_49313
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798592870354897835000593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1199061913569931890000395 1798592870354897835000593)
  ·
    refine ⟨1348944652766173376250445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1798592870354897835000593 1348944652766173376250445)
    ·
      refine ⟨505854244787315016093917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1348944652766173376250445 505854244787315016093917)
      ·
        refine ⟨189695341795243131035219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 505854244787315016093917 189695341795243131035219)
        ·
          refine ⟨284543012692864696552829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189695341795243131035219 284543012692864696552829)
          ·
            refine ⟨106703629759824261207311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284543012692864696552829 106703629759824261207311)
            ·
              refine ⟨160055444639736391810967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106703629759824261207311 160055444639736391810967)
              ·
                refine ⟨240083166959604587716451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160055444639736391810967 240083166959604587716451)
                ·
                  refine ⟨360124750439406881574677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240083166959604587716451 360124750439406881574677)
                  ·
                    refine ⟨16880847676847197573813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 360124750439406881574677 16880847676847197573813)
                    ·
                      rfl

theorem cell22_49313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_49313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49313 prefixEnd_49313 := by exact prefixLift 49313
  have htrace : WordTrace (prefixWord ++ tailWord_49313) baseStart_49313 baseEnd_49313 := by
    simpa [prefixWord, tailWord_49313, baseEnd_49313] using wordTrace_append hprefix tailTrace_49313
  have hstable : (prefixWord ++ tailWord_49313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49313).length < 2 ^ (prefixWord ++ tailWord_49313).sum := by decide
  have hdescent : baseEnd_49313 < baseStart_49313 := by decide
  rcases family_descends (prefixWord ++ tailWord_49313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49319 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 1, 4]
def baseStart_49319 : Nat := 118140960795 + 49319 * 2 ^ 59
def prefixEnd_49319 : Nat := 4983230072969 + 3 ^ 40 * 49319 * 2
def baseEnd_49319 : Nat := 16882901599465181923795

theorem tailTrace_49319 : CollatzResearch.WordTrace tailWord_49319 prefixEnd_49319 16882901599465181923795 := by
  unfold tailWord_49319
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798811708333160859719011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1199207805555440573146007 1798811708333160859719011)
  ·
    refine ⟨2698217562499741289578517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798811708333160859719011 2698217562499741289578517)
    ·
      refine ⟨126478948242175372948993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2698217562499741289578517 126478948242175372948993)
      ·
        refine ⟨94859211181631529711745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126478948242175372948993 94859211181631529711745)
        ·
          refine ⟨71144408386223647283809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94859211181631529711745 71144408386223647283809)
          ·
            refine ⟨53358306289667735462857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71144408386223647283809 53358306289667735462857)
            ·
              refine ⟨40018729717250801597143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53358306289667735462857 40018729717250801597143)
              ·
                refine ⟨60028094575876202395715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40018729717250801597143 60028094575876202395715)
                ·
                  refine ⟨90042141863814303593573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60028094575876202395715 90042141863814303593573)
                  ·
                    refine ⟨16882901599465181923795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90042141863814303593573 16882901599465181923795)
                    ·
                      rfl

theorem cell22_49319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_49319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49319 prefixEnd_49319 := by exact prefixLift 49319
  have htrace : WordTrace (prefixWord ++ tailWord_49319) baseStart_49319 baseEnd_49319 := by
    simpa [prefixWord, tailWord_49319, baseEnd_49319] using wordTrace_append hprefix tailTrace_49319
  have hstable : (prefixWord ++ tailWord_49319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49319).length < 2 ^ (prefixWord ++ tailWord_49319).sum := by decide
  have hdescent : baseEnd_49319 < baseStart_49319 := by decide
  rcases family_descends (prefixWord ++ tailWord_49319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_49371 : Nat := 118140960795 + 49371 * 2 ^ 59
def prefixEnd_49371 : Nat := 4983230072969 + 3 ^ 40 * 49371 * 2
def baseEnd_49371 : Nat := 16900702262154379623635

theorem tailTrace_49371 : CollatzResearch.WordTrace tailWord_49371 prefixEnd_49371 16900702262154379623635 := by
  unfold tailWord_49371
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800708304144773740611967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1200472202763182493741311 1800708304144773740611967)
  ·
    refine ⟨2701062456217160610917951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800708304144773740611967 2701062456217160610917951)
    ·
      refine ⟨4051593684325740916376927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701062456217160610917951 4051593684325740916376927)
      ·
        refine ⟨6077390526488611374565391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051593684325740916376927 6077390526488611374565391)
        ·
          refine ⟨9116085789732917061848087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077390526488611374565391 9116085789732917061848087)
          ·
            refine ⟨13674128684599375592772131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116085789732917061848087 13674128684599375592772131)
            ·
              refine ⟨20511193026899063389158197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13674128684599375592772131 20511193026899063389158197)
              ·
                refine ⟨1922924346271787192733581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20511193026899063389158197 1922924346271787192733581)
                ·
                  refine ⟨721096629851920197275093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1922924346271787192733581 721096629851920197275093)
                  ·
                    refine ⟨16900702262154379623635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 721096629851920197275093 16900702262154379623635)
                    ·
                      rfl

theorem cell22_49371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_49371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49371 prefixEnd_49371 := by exact prefixLift 49371
  have htrace : WordTrace (prefixWord ++ tailWord_49371) baseStart_49371 baseEnd_49371 := by
    simpa [prefixWord, tailWord_49371, baseEnd_49371] using wordTrace_append hprefix tailTrace_49371
  have hstable : (prefixWord ++ tailWord_49371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49371).length < 2 ^ (prefixWord ++ tailWord_49371).sum := by decide
  have hdescent : baseEnd_49371 < baseStart_49371 := by decide
  rcases family_descends (prefixWord ++ tailWord_49371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49418 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_49418 : Nat := 118140960795 + 49418 * 2 ^ 59
def prefixEnd_49418 : Nat := 4983230072969 + 3 ^ 40 * 49418 * 2
def baseEnd_49418 : Nat := 5638930440887307899497

theorem tailTrace_49418 : CollatzResearch.WordTrace tailWord_49418 prefixEnd_49418 5638930440887307899497 := by
  unfold tailWord_49418
  simp only [CollatzResearch.WordTrace]
  refine ⟨450605633743625191893227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1201615023316333845048605 450605633743625191893227)
  ·
    refine ⟨675908450615437787839841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450605633743625191893227 675908450615437787839841)
    ·
      refine ⟨506931337961578340879881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675908450615437787839841 506931337961578340879881)
      ·
        refine ⟨380198503471183755659911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506931337961578340879881 380198503471183755659911)
        ·
          refine ⟨570297755206775633489867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380198503471183755659911 570297755206775633489867)
          ·
            refine ⟨855446632810163450234801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570297755206775633489867 855446632810163450234801)
            ·
              refine ⟨641584974607622587676101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855446632810163450234801 641584974607622587676101)
              ·
                refine ⟨120297182738929235189269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 641584974607622587676101 120297182738929235189269)
                ·
                  refine ⟨5638930440887307899497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120297182738929235189269 5638930440887307899497)
                  ·
                    rfl

theorem cell22_49418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_49418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49418 prefixEnd_49418 := by exact prefixLift 49418
  have htrace : WordTrace (prefixWord ++ tailWord_49418) baseStart_49418 baseEnd_49418 := by
    simpa [prefixWord, tailWord_49418, baseEnd_49418] using wordTrace_append hprefix tailTrace_49418
  have hstable : (prefixWord ++ tailWord_49418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49418).length < 2 ^ (prefixWord ++ tailWord_49418).sum := by decide
  have hdescent : baseEnd_49418 < baseStart_49418 := by decide
  rcases family_descends (prefixWord ++ tailWord_49418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49452 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 4]
def baseStart_49452 : Nat := 118140960795 + 49452 * 2 ^ 59
def prefixEnd_49452 : Nat := 4983230072969 + 3 ^ 40 * 49452 * 2
def baseEnd_49452 : Nat := 5642810072499056116129

theorem tailTrace_49452 : CollatzResearch.WordTrace tailWord_49452 prefixEnd_49452 5642810072499056116129 := by
  unfold tailWord_49452
  simp only [CollatzResearch.WordTrace]
  refine ⟨901831308425662287155305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1202441744567549716207073 901831308425662287155305)
  ·
    refine ⟨676373481319246715366479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 901831308425662287155305 676373481319246715366479)
    ·
      refine ⟨1014560221978870073049719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676373481319246715366479 1014560221978870073049719)
      ·
        refine ⟨1521840332968305109574579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014560221978870073049719 1521840332968305109574579)
        ·
          refine ⟨2282760499452457664361869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521840332968305109574579 2282760499452457664361869)
          ·
            refine ⟨856035187294671624135701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2282760499452457664361869 856035187294671624135701)
            ·
              refine ⟨40126649404437732381361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 856035187294671624135701 40126649404437732381361)
              ·
                refine ⟨30094987053328299286021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40126649404437732381361 30094987053328299286021)
                ·
                  refine ⟨5642810072499056116129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30094987053328299286021 5642810072499056116129)
                  ·
                    rfl

theorem cell22_49452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_49452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49452 prefixEnd_49452 := by exact prefixLift 49452
  have htrace : WordTrace (prefixWord ++ tailWord_49452) baseStart_49452 baseEnd_49452 := by
    simpa [prefixWord, tailWord_49452, baseEnd_49452] using wordTrace_append hprefix tailTrace_49452
  have hstable : (prefixWord ++ tailWord_49452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49452).length < 2 ^ (prefixWord ++ tailWord_49452).sum := by decide
  have hdescent : baseEnd_49452 < baseStart_49452 := by decide
  rcases family_descends (prefixWord ++ tailWord_49452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49495 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 5, 3]
def baseStart_49495 : Nat := 118140960795 + 49495 * 2 ^ 59
def prefixEnd_49495 : Nat := 4983230072969 + 3 ^ 40 * 49495 * 2
def baseEnd_49495 : Nat := 16943149996259389523255

theorem tailTrace_49495 : CollatzResearch.WordTrace tailWord_49495 prefixEnd_49495 16943149996259389523255 := by
  unfold tailWord_49495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805230955695542918125939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1203487303797028612083959 1805230955695542918125939)
  ·
    refine ⟨2707846433543314377188909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1805230955695542918125939 2707846433543314377188909)
    ·
      refine ⟨1015442412578742891445841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2707846433543314377188909 1015442412578742891445841)
      ·
        refine ⟨761581809434057168584381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015442412578742891445841 761581809434057168584381)
        ·
          refine ⟨285593178537771438219143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761581809434057168584381 285593178537771438219143)
          ·
            refine ⟨428389767806657157328715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285593178537771438219143 428389767806657157328715)
            ·
              refine ⟨642584651709985735993073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428389767806657157328715 642584651709985735993073)
              ·
                refine ⟨481938488782489301994805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642584651709985735993073 481938488782489301994805)
                ·
                  refine ⟨45181733323358372062013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481938488782489301994805 45181733323358372062013)
                  ·
                    refine ⟨16943149996259389523255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45181733323358372062013 16943149996259389523255)
                    ·
                      rfl

theorem cell22_49495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_49495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49495 prefixEnd_49495 := by exact prefixLift 49495
  have htrace : WordTrace (prefixWord ++ tailWord_49495) baseStart_49495 baseEnd_49495 := by
    simpa [prefixWord, tailWord_49495, baseEnd_49495] using wordTrace_append hprefix tailTrace_49495
  have hstable : (prefixWord ++ tailWord_49495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49495).length < 2 ^ (prefixWord ++ tailWord_49495).sum := by decide
  have hdescent : baseEnd_49495 < baseStart_49495 := by decide
  rcases family_descends (prefixWord ++ tailWord_49495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49512 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_49512 : Nat := 118140960795 + 49512 * 2 ^ 59
def prefixEnd_49512 : Nat := 4983230072969 + 3 ^ 40 * 49512 * 2
def baseEnd_49512 : Nat := 16948969443677011848203

theorem tailTrace_49512 : CollatzResearch.WordTrace tailWord_49512 prefixEnd_49512 16948969443677011848203 := by
  unfold tailWord_49512
  simp only [CollatzResearch.WordTrace]
  refine ⟨902925498316977410747395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1203900664422636547663193 902925498316977410747395)
  ·
    refine ⟨1354388247475466116121093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 902925498316977410747395 1354388247475466116121093)
    ·
      refine ⟨253947796401649896772705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1354388247475466116121093 253947796401649896772705)
      ·
        refine ⟨190460847301237422579529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253947796401649896772705 190460847301237422579529)
        ·
          refine ⟨142845635475928066934647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190460847301237422579529 142845635475928066934647)
          ·
            refine ⟨214268453213892100401971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142845635475928066934647 214268453213892100401971)
            ·
              refine ⟨321402679820838150602957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214268453213892100401971 321402679820838150602957)
              ·
                refine ⟨120526004932814306476109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321402679820838150602957 120526004932814306476109)
                ·
                  refine ⟨45197251849805364928541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120526004932814306476109 45197251849805364928541)
                  ·
                    refine ⟨16948969443677011848203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45197251849805364928541 16948969443677011848203)
                    ·
                      rfl

theorem cell22_49512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_49512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49512 prefixEnd_49512 := by exact prefixLift 49512
  have htrace : WordTrace (prefixWord ++ tailWord_49512) baseStart_49512 baseEnd_49512 := by
    simpa [prefixWord, tailWord_49512, baseEnd_49512] using wordTrace_append hprefix tailTrace_49512
  have hstable : (prefixWord ++ tailWord_49512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49512).length < 2 ^ (prefixWord ++ tailWord_49512).sum := by decide
  have hdescent : baseEnd_49512 < baseStart_49512 := by decide
  rcases family_descends (prefixWord ++ tailWord_49512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49576 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_49576 : Nat := 118140960795 + 49576 * 2 ^ 59
def prefixEnd_49576 : Nat := 4983230072969 + 3 ^ 40 * 49576 * 2
def baseEnd_49576 : Nat := 5656959317200726082669

theorem tailTrace_49576 : CollatzResearch.WordTrace tailWord_49576 prefixEnd_49576 5656959317200726082669 := by
  unfold tailWord_49576
  simp only [CollatzResearch.WordTrace]
  refine ⟨904092634201046875912291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1205456845601395834549721 904092634201046875912291)
  ·
    refine ⟨1356138951301570313868437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904092634201046875912291 1356138951301570313868437)
    ·
      refine ⟨63569013342261108462583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1356138951301570313868437 63569013342261108462583)
      ·
        refine ⟨95353520013391662693875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63569013342261108462583 95353520013391662693875)
        ·
          refine ⟨143030280020087494040813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95353520013391662693875 143030280020087494040813)
          ·
            refine ⟨53636355007532810265305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143030280020087494040813 53636355007532810265305)
            ·
              refine ⟨40227266255649607698979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53636355007532810265305 40227266255649607698979)
              ·
                refine ⟨60340899383474411548469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40227266255649607698979 60340899383474411548469)
                ·
                  refine ⟨5656959317200726082669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60340899383474411548469 5656959317200726082669)
                  ·
                    rfl

theorem cell22_49576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_49576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49576 prefixEnd_49576 := by exact prefixLift 49576
  have htrace : WordTrace (prefixWord ++ tailWord_49576) baseStart_49576 baseEnd_49576 := by
    simpa [prefixWord, tailWord_49576, baseEnd_49576] using wordTrace_append hprefix tailTrace_49576
  have hstable : (prefixWord ++ tailWord_49576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49576).length < 2 ^ (prefixWord ++ tailWord_49576).sum := by decide
  have hdescent : baseEnd_49576 < baseStart_49576 := by decide
  rcases family_descends (prefixWord ++ tailWord_49576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49621 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 4]
def baseStart_49621 : Nat := 118140960795 + 49621 * 2 ^ 59
def prefixEnd_49621 : Nat := 4983230072969 + 3 ^ 40 * 49621 * 2
def baseEnd_49621 : Nat := 5662094123745686957623

theorem tailTrace_49621 : CollatzResearch.WordTrace tailWord_49621 prefixEnd_49621 5662094123745686957623 := by
  unfold tailWord_49621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1809826553239066437212717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1206551035492710958141811 1809826553239066437212717)
  ·
    refine ⟨678684957464649913954769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1809826553239066437212717 678684957464649913954769)
    ·
      refine ⟨509013718098487435466077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678684957464649913954769 509013718098487435466077)
      ·
        refine ⟨190880144286932788299779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509013718098487435466077 190880144286932788299779)
        ·
          refine ⟨286320216430399182449669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190880144286932788299779 286320216430399182449669)
          ·
            refine ⟨53685040580699846709313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286320216430399182449669 53685040580699846709313)
            ·
              refine ⟨40263780435524885031985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53685040580699846709313 40263780435524885031985)
              ·
                refine ⟨30197835326643663773989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40263780435524885031985 30197835326643663773989)
                ·
                  refine ⟨5662094123745686957623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30197835326643663773989 5662094123745686957623)
                  ·
                    rfl

theorem cell22_49621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_49621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49621 prefixEnd_49621 := by exact prefixLift 49621
  have htrace : WordTrace (prefixWord ++ tailWord_49621) baseStart_49621 baseEnd_49621 := by
    simpa [prefixWord, tailWord_49621, baseEnd_49621] using wordTrace_append hprefix tailTrace_49621
  have hstable : (prefixWord ++ tailWord_49621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49621).length < 2 ^ (prefixWord ++ tailWord_49621).sum := by decide
  have hdescent : baseEnd_49621 < baseStart_49621 := by decide
  rcases family_descends (prefixWord ++ tailWord_49621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49660 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_49660 : Nat := 118140960795 + 49660 * 2 ^ 59
def prefixEnd_49660 : Nat := 4983230072969 + 3 ^ 40 * 49660 * 2
def baseEnd_49660 : Nat := 5666544289417986382583

theorem tailTrace_49660 : CollatzResearch.WordTrace tailWord_49660 prefixEnd_49660 5666544289417986382583 := by
  unfold tailWord_49660
  simp only [CollatzResearch.WordTrace]
  refine ⟨905624500048888048941217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1207499333398517398588289 905624500048888048941217)
  ·
    refine ⟨679218375036666036705913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905624500048888048941217 679218375036666036705913)
    ·
      refine ⟨509413781277499527529435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 679218375036666036705913 509413781277499527529435)
      ·
        refine ⟨764120671916249291294153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509413781277499527529435 764120671916249291294153)
        ·
          refine ⟨573090503937186968470615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764120671916249291294153 573090503937186968470615)
          ·
            refine ⟨859635755905780452705923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573090503937186968470615 859635755905780452705923)
            ·
              refine ⟨1289453633858670679058885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859635755905780452705923 1289453633858670679058885)
              ·
                refine ⟨241772556348500752323541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1289453633858670679058885 241772556348500752323541)
                ·
                  refine ⟨5666544289417986382583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241772556348500752323541 5666544289417986382583)
                  ·
                    rfl

theorem cell22_49660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_49660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49660 prefixEnd_49660 := by exact prefixLift 49660
  have htrace : WordTrace (prefixWord ++ tailWord_49660) baseStart_49660 baseEnd_49660 := by
    simpa [prefixWord, tailWord_49660, baseEnd_49660] using wordTrace_append hprefix tailTrace_49660
  have hstable : (prefixWord ++ tailWord_49660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49660).length < 2 ^ (prefixWord ++ tailWord_49660).sum := by decide
  have hdescent : baseEnd_49660 < baseStart_49660 := by decide
  rcases family_descends (prefixWord ++ tailWord_49660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49670 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_49670 : Nat := 118140960795 + 49670 * 2 ^ 59
def prefixEnd_49670 : Nat := 4983230072969 + 3 ^ 40 * 49670 * 2
def baseEnd_49670 : Nat := 17003056072617266397719

theorem tailTrace_49670 : CollatzResearch.WordTrace tailWord_49670 prefixEnd_49670 17003056072617266397719 := by
  unfold tailWord_49670
  simp only [CollatzResearch.WordTrace]
  refine ⟨56612929064423368929577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1207742486707698537164309 56612929064423368929577)
  ·
    refine ⟨42459696798317526697183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56612929064423368929577 42459696798317526697183)
    ·
      refine ⟨63689545197476290045775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42459696798317526697183 63689545197476290045775)
      ·
        refine ⟨95534317796214435068663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63689545197476290045775 95534317796214435068663)
        ·
          refine ⟨143301476694321652602995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95534317796214435068663 143301476694321652602995)
          ·
            refine ⟨214952215041482478904493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143301476694321652602995 214952215041482478904493)
            ·
              refine ⟨80607080640555929589185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214952215041482478904493 80607080640555929589185)
              ·
                refine ⟨60455310480416947191889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80607080640555929589185 60455310480416947191889)
                ·
                  refine ⟨45341482860312710393917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60455310480416947191889 45341482860312710393917)
                  ·
                    refine ⟨17003056072617266397719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45341482860312710393917 17003056072617266397719)
                    ·
                      rfl

theorem cell22_49670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_49670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49670 prefixEnd_49670 := by exact prefixLift 49670
  have htrace : WordTrace (prefixWord ++ tailWord_49670) baseStart_49670 baseEnd_49670 := by
    simpa [prefixWord, tailWord_49670, baseEnd_49670] using wordTrace_append hprefix tailTrace_49670
  have hstable : (prefixWord ++ tailWord_49670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49670).length < 2 ^ (prefixWord ++ tailWord_49670).sum := by decide
  have hdescent : baseEnd_49670 < baseStart_49670 := by decide
  rcases family_descends (prefixWord ++ tailWord_49670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49692 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_49692 : Nat := 118140960795 + 49692 * 2 ^ 59
def prefixEnd_49692 : Nat := 4983230072969 + 3 ^ 40 * 49692 * 2
def baseEnd_49692 : Nat := 17010587122216542347651

theorem tailTrace_49692 : CollatzResearch.WordTrace tailWord_49692 prefixEnd_49692 17010587122216542347651 := by
  unfold tailWord_49692
  simp only [CollatzResearch.WordTrace]
  refine ⟨906208067990922781523665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1208277423987897042031553 906208067990922781523665)
  ·
    refine ⟨679656050993192086142749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906208067990922781523665 679656050993192086142749)
    ·
      refine ⟨254871019122447032303531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 679656050993192086142749 254871019122447032303531)
      ·
        refine ⟨382306528683670548455297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254871019122447032303531 382306528683670548455297)
        ·
          refine ⟨286729896512752911341473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382306528683670548455297 286729896512752911341473)
          ·
            refine ⟨215047422384564683506105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286729896512752911341473 215047422384564683506105)
            ·
              refine ⟨161285566788423512629579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215047422384564683506105 161285566788423512629579)
              ·
                refine ⟨241928350182635268944369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161285566788423512629579 241928350182635268944369)
                ·
                  refine ⟨181446262636976451708277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241928350182635268944369 181446262636976451708277)
                  ·
                    refine ⟨17010587122216542347651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181446262636976451708277 17010587122216542347651)
                    ·
                      rfl

theorem cell22_49692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_49692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49692 prefixEnd_49692 := by exact prefixLift 49692
  have htrace : WordTrace (prefixWord ++ tailWord_49692) baseStart_49692 baseEnd_49692 := by
    simpa [prefixWord, tailWord_49692, baseEnd_49692] using wordTrace_append hprefix tailTrace_49692
  have hstable : (prefixWord ++ tailWord_49692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49692).length < 2 ^ (prefixWord ++ tailWord_49692).sum := by decide
  have hdescent : baseEnd_49692 < baseStart_49692 := by decide
  rcases family_descends (prefixWord ++ tailWord_49692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49724 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_49724 : Nat := 118140960795 + 49724 * 2 ^ 59
def prefixEnd_49724 : Nat := 4983230072969 + 3 ^ 40 * 49724 * 2
def baseEnd_49724 : Nat := 17021541376179125547553

theorem tailTrace_49724 : CollatzResearch.WordTrace tailWord_49724 prefixEnd_49724 17021541376179125547553 := by
  unfold tailWord_49724
  simp only [CollatzResearch.WordTrace]
  refine ⟨906791635932957514106113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1209055514577276685474817 906791635932957514106113)
  ·
    refine ⟨680093726949718135579585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906791635932957514106113 680093726949718135579585)
    ·
      refine ⟨510070295212288601684689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680093726949718135579585 510070295212288601684689)
      ·
        refine ⟨382552721409216451263517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510070295212288601684689 382552721409216451263517)
        ·
          refine ⟨143457270528456169223819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382552721409216451263517 143457270528456169223819)
          ·
            refine ⟨215185905792684253835729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143457270528456169223819 215185905792684253835729)
            ·
              refine ⟨161389429344513190376797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215185905792684253835729 161389429344513190376797)
              ·
                refine ⟨60521036004192446391299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161389429344513190376797 60521036004192446391299)
                ·
                  refine ⟨90781554006288669586949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60521036004192446391299 90781554006288669586949)
                  ·
                    refine ⟨17021541376179125547553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90781554006288669586949 17021541376179125547553)
                    ·
                      rfl

theorem cell22_49724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_49724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49724 prefixEnd_49724 := by exact prefixLift 49724
  have htrace : WordTrace (prefixWord ++ tailWord_49724) baseStart_49724 baseEnd_49724 := by
    simpa [prefixWord, tailWord_49724, baseEnd_49724] using wordTrace_append hprefix tailTrace_49724
  have hstable : (prefixWord ++ tailWord_49724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49724).length < 2 ^ (prefixWord ++ tailWord_49724).sum := by decide
  have hdescent : baseEnd_49724 < baseStart_49724 := by decide
  rcases family_descends (prefixWord ++ tailWord_49724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49732 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_49732 : Nat := 118140960795 + 49732 * 2 ^ 59
def prefixEnd_49732 : Nat := 4983230072969 + 3 ^ 40 * 49732 * 2
def baseEnd_49732 : Nat := 17024279939669771347529

theorem tailTrace_49732 : CollatzResearch.WordTrace tailWord_49732 prefixEnd_49732 17024279939669771347529 := by
  unfold tailWord_49732
  simp only [CollatzResearch.WordTrace]
  refine ⟨906937527918466197251725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1209250037224621596335633 906937527918466197251725)
  ·
    refine ⟨340101572969424823969397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 906937527918466197251725 340101572969424823969397)
    ·
      refine ⟨31884522465883577247131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 340101572969424823969397 31884522465883577247131)
      ·
        refine ⟨47826783698825365870697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31884522465883577247131 47826783698825365870697)
        ·
          refine ⟨35870087774119024403023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47826783698825365870697 35870087774119024403023)
          ·
            refine ⟨53805131661178536604535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35870087774119024403023 53805131661178536604535)
            ·
              refine ⟨80707697491767804906803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53805131661178536604535 80707697491767804906803)
              ·
                refine ⟨121061546237651707360205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80707697491767804906803 121061546237651707360205)
                ·
                  refine ⟨45398079839119390260077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121061546237651707360205 45398079839119390260077)
                  ·
                    refine ⟨17024279939669771347529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45398079839119390260077 17024279939669771347529)
                    ·
                      rfl

theorem cell22_49732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_49732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49732 prefixEnd_49732 := by exact prefixLift 49732
  have htrace : WordTrace (prefixWord ++ tailWord_49732) baseStart_49732 baseEnd_49732 := by
    simpa [prefixWord, tailWord_49732, baseEnd_49732] using wordTrace_append hprefix tailTrace_49732
  have hstable : (prefixWord ++ tailWord_49732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49732).length < 2 ^ (prefixWord ++ tailWord_49732).sum := by decide
  have hdescent : baseEnd_49732 < baseStart_49732 := by decide
  rcases family_descends (prefixWord ++ tailWord_49732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49797 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_49797 : Nat := 118140960795 + 49797 * 2 ^ 59
def prefixEnd_49797 : Nat := 4983230072969 + 3 ^ 40 * 49797 * 2
def baseEnd_49797 : Nat := 17046530768031268472329

theorem tailTrace_49797 : CollatzResearch.WordTrace tailWord_49797 prefixEnd_49797 17046530768031268472329 := by
  unfold tailWord_49797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816245800601448495619645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210830533734298997079763 1816245800601448495619645)
  ·
    refine ⟨681092175225543185857367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1816245800601448495619645 681092175225543185857367)
    ·
      refine ⟨1021638262838314778786051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681092175225543185857367 1021638262838314778786051)
      ·
        refine ⟨1532457394257472168179077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021638262838314778786051 1532457394257472168179077)
        ·
          refine ⟨287335761423276031533577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1532457394257472168179077 287335761423276031533577)
          ·
            refine ⟨215501821067457023650183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287335761423276031533577 215501821067457023650183)
            ·
              refine ⟨323252731601185535475275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215501821067457023650183 323252731601185535475275)
              ·
                refine ⟨484879097401778303212913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323252731601185535475275 484879097401778303212913)
                ·
                  refine ⟨363659323051333727409685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484879097401778303212913 363659323051333727409685)
                  ·
                    refine ⟨17046530768031268472329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 363659323051333727409685 17046530768031268472329)
                    ·
                      rfl

theorem cell22_49797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_49797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49797 prefixEnd_49797 := by exact prefixLift 49797
  have htrace : WordTrace (prefixWord ++ tailWord_49797) baseStart_49797 baseEnd_49797 := by
    simpa [prefixWord, tailWord_49797, baseEnd_49797] using wordTrace_append hprefix tailTrace_49797
  have hstable : (prefixWord ++ tailWord_49797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49797).length < 2 ^ (prefixWord ++ tailWord_49797).sum := by decide
  have hdescent : baseEnd_49797 < baseStart_49797 := by decide
  rcases family_descends (prefixWord ++ tailWord_49797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49799 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 3, 3]
def baseStart_49799 : Nat := 118140960795 + 49799 * 2 ^ 59
def prefixEnd_49799 : Nat := 4983230072969 + 3 ^ 40 * 49799 * 2
def baseEnd_49799 : Nat := 17047215408903929922323

theorem tailTrace_49799 : CollatzResearch.WordTrace tailWord_49799 prefixEnd_49799 17047215408903929922323 := by
  unfold tailWord_49799
  simp only [CollatzResearch.WordTrace]
  refine ⟨1816318746594202837192451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210879164396135224794967 1816318746594202837192451)
  ·
    refine ⟨2724478119891304255788677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1816318746594202837192451 2724478119891304255788677)
    ·
      refine ⟨510839647479619547960377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2724478119891304255788677 510839647479619547960377)
      ·
        refine ⟨383129735609714660970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510839647479619547960377 383129735609714660970283)
        ·
          refine ⟨574694603414571991455425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383129735609714660970283 574694603414571991455425)
          ·
            refine ⟨431020952560928993591569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574694603414571991455425 431020952560928993591569)
            ·
              refine ⟨323265714420696745193677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431020952560928993591569 323265714420696745193677)
              ·
                refine ⟨121224642907761279447629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323265714420696745193677 121224642907761279447629)
                ·
                  refine ⟨45459241090410479792861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121224642907761279447629 45459241090410479792861)
                  ·
                    refine ⟨17047215408903929922323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45459241090410479792861 17047215408903929922323)
                    ·
                      rfl

theorem cell22_49799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_49799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49799 prefixEnd_49799 := by exact prefixLift 49799
  have htrace : WordTrace (prefixWord ++ tailWord_49799) baseStart_49799 baseEnd_49799 := by
    simpa [prefixWord, tailWord_49799, baseEnd_49799] using wordTrace_append hprefix tailTrace_49799
  have hstable : (prefixWord ++ tailWord_49799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49799).length < 2 ^ (prefixWord ++ tailWord_49799).sum := by decide
  have hdescent : baseEnd_49799 < baseStart_49799 := by decide
  rcases family_descends (prefixWord ++ tailWord_49799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49904 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_49904 : Nat := 118140960795 + 49904 * 2 ^ 59
def prefixEnd_49904 : Nat := 4983230072969 + 3 ^ 40 * 49904 * 2
def baseEnd_49904 : Nat := 17083159054718656047001

theorem tailTrace_49904 : CollatzResearch.WordTrace tailWord_49904 prefixEnd_49904 17083159054718656047001 := by
  unfold tailWord_49904
  simp only [CollatzResearch.WordTrace]
  refine ⟨910074205606902884882383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1213432274142537179843177 910074205606902884882383)
  ·
    refine ⟨1365111308410354327323575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910074205606902884882383 1365111308410354327323575)
    ·
      refine ⟨2047666962615531490985363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365111308410354327323575 2047666962615531490985363)
      ·
        refine ⟨3071500443923297236478045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047666962615531490985363 3071500443923297236478045)
        ·
          refine ⟨1151812666471236463679267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3071500443923297236478045 1151812666471236463679267)
          ·
            refine ⟨1727718999706854695518901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151812666471236463679267 1727718999706854695518901)
            ·
              refine ⟨161973656222517627704897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1727718999706854695518901 161973656222517627704897)
              ·
                refine ⟨121480242166888220778673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161973656222517627704897 121480242166888220778673)
                ·
                  refine ⟨91110181625166165584005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121480242166888220778673 91110181625166165584005)
                  ·
                    refine ⟨17083159054718656047001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91110181625166165584005 17083159054718656047001)
                    ·
                      rfl

theorem cell22_49904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_49904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49904 prefixEnd_49904 := by exact prefixLift 49904
  have htrace : WordTrace (prefixWord ++ tailWord_49904) baseStart_49904 baseEnd_49904 := by
    simpa [prefixWord, tailWord_49904, baseEnd_49904] using wordTrace_append hprefix tailTrace_49904
  have hstable : (prefixWord ++ tailWord_49904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49904).length < 2 ^ (prefixWord ++ tailWord_49904).sum := by decide
  have hdescent : baseEnd_49904 < baseStart_49904 := by decide
  rcases family_descends (prefixWord ++ tailWord_49904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49906 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_49906 : Nat := 118140960795 + 49906 * 2 ^ 59
def prefixEnd_49906 : Nat := 4983230072969 + 3 ^ 40 * 49906 * 2
def baseEnd_49906 : Nat := 17083843695591317496995

theorem tailTrace_49906 : CollatzResearch.WordTrace tailWord_49906 prefixEnd_49906 17083843695591317496995 := by
  unfold tailWord_49906
  simp only [CollatzResearch.WordTrace]
  refine ⟨455055339301640027834393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1213480904804373407558381 455055339301640027834393)
  ·
    refine ⟨341291504476230020875795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455055339301640027834393 341291504476230020875795)
    ·
      refine ⟨511937256714345031313693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341291504476230020875795 511937256714345031313693)
      ·
        refine ⟨191976471267879386742635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511937256714345031313693 191976471267879386742635)
        ·
          refine ⟨287964706901819080113953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191976471267879386742635 287964706901819080113953)
          ·
            refine ⟨215973530176364310085465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287964706901819080113953 215973530176364310085465)
            ·
              refine ⟨161980147632273232564099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215973530176364310085465 161980147632273232564099)
              ·
                refine ⟨242970221448409848846149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161980147632273232564099 242970221448409848846149)
                ·
                  refine ⟨45556916521576846658653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242970221448409848846149 45556916521576846658653)
                  ·
                    refine ⟨17083843695591317496995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45556916521576846658653 17083843695591317496995)
                    ·
                      rfl

theorem cell22_49906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_49906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49906 prefixEnd_49906 := by exact prefixLift 49906
  have htrace : WordTrace (prefixWord ++ tailWord_49906) baseStart_49906 baseEnd_49906 := by
    simpa [prefixWord, tailWord_49906, baseEnd_49906] using wordTrace_append hprefix tailTrace_49906
  have hstable : (prefixWord ++ tailWord_49906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49906).length < 2 ^ (prefixWord ++ tailWord_49906).sum := by decide
  have hdescent : baseEnd_49906 < baseStart_49906 := by decide
  rcases family_descends (prefixWord ++ tailWord_49906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49966 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_49966 : Nat := 118140960795 + 49966 * 2 ^ 59
def prefixEnd_49966 : Nat := 4983230072969 + 3 ^ 40 * 49966 * 2
def baseEnd_49966 : Nat := 17104382921771160996811

theorem tailTrace_49966 : CollatzResearch.WordTrace tailWord_49966 prefixEnd_49966 17104382921771160996811 := by
  unfold tailWord_49966
  simp only [CollatzResearch.WordTrace]
  refine ⟨227801217123648794815219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1214939824659460239014501 227801217123648794815219)
  ·
    refine ⟨341701825685473192222829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227801217123648794815219 341701825685473192222829)
    ·
      refine ⟨128138184632052447083561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341701825685473192222829 128138184632052447083561)
      ·
        refine ⟨96103638474039335312671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128138184632052447083561 96103638474039335312671)
        ·
          refine ⟨144155457711059002969007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96103638474039335312671 144155457711059002969007)
          ·
            refine ⟨216233186566588504453511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144155457711059002969007 216233186566588504453511)
            ·
              refine ⟨324349779849882756680267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216233186566588504453511 324349779849882756680267)
              ·
                refine ⟨486524669774824135020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324349779849882756680267 486524669774824135020401)
                ·
                  refine ⟨364893502331118101265301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 486524669774824135020401 364893502331118101265301)
                  ·
                    refine ⟨17104382921771160996811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 364893502331118101265301 17104382921771160996811)
                    ·
                      rfl

theorem cell22_49966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_49966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49966 prefixEnd_49966 := by exact prefixLift 49966
  have htrace : WordTrace (prefixWord ++ tailWord_49966) baseStart_49966 baseEnd_49966 := by
    simpa [prefixWord, tailWord_49966, baseEnd_49966] using wordTrace_append hprefix tailTrace_49966
  have hstable : (prefixWord ++ tailWord_49966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49966).length < 2 ^ (prefixWord ++ tailWord_49966).sum := by decide
  have hdescent : baseEnd_49966 < baseStart_49966 := by decide
  rcases family_descends (prefixWord ++ tailWord_49966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49985 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_49985 : Nat := 118140960795 + 49985 * 2 ^ 59
def prefixEnd_49985 : Nat := 4983230072969 + 3 ^ 40 * 49985 * 2
def baseEnd_49985 : Nat := 17110887010061444771753

theorem tailTrace_49985 : CollatzResearch.WordTrace tailWord_49985 prefixEnd_49985 17110887010061444771753 := by
  unfold tailWord_49985
  simp only [CollatzResearch.WordTrace]
  refine ⟨1823102723920356603463409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1215401815946904402308939 1823102723920356603463409)
  ·
    refine ⟨1367327042940267452597557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1823102723920356603463409 1367327042940267452597557)
    ·
      refine ⟨128186910275650073681021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1367327042940267452597557 128186910275650073681021)
      ·
        refine ⟨48070091353368777630383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128186910275650073681021 48070091353368777630383)
        ·
          refine ⟨72105137030053166445575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48070091353368777630383 72105137030053166445575)
          ·
            refine ⟨108157705545079749668363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72105137030053166445575 108157705545079749668363)
            ·
              refine ⟨162236558317619624502545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108157705545079749668363 162236558317619624502545)
              ·
                refine ⟨121677418738214718376909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162236558317619624502545 121677418738214718376909)
                ·
                  refine ⟨45629032026830519391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121677418738214718376909 45629032026830519391341)
                  ·
                    refine ⟨17110887010061444771753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45629032026830519391341 17110887010061444771753)
                    ·
                      rfl

theorem cell22_49985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_49985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_49985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_49985 prefixEnd_49985 := by exact prefixLift 49985
  have htrace : WordTrace (prefixWord ++ tailWord_49985) baseStart_49985 baseEnd_49985 := by
    simpa [prefixWord, tailWord_49985, baseEnd_49985] using wordTrace_append hprefix tailTrace_49985
  have hstable : (prefixWord ++ tailWord_49985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49985).length < 2 ^ (prefixWord ++ tailWord_49985).sum := by decide
  have hdescent : baseEnd_49985 < baseStart_49985 := by decide
  rcases family_descends (prefixWord ++ tailWord_49985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50041 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_50041 : Nat := 118140960795 + 50041 * 2 ^ 59
def prefixEnd_50041 : Nat := 4983230072969 + 3 ^ 40 * 50041 * 2
def baseEnd_50041 : Nat := 17130056954495965371581

theorem tailTrace_50041 : CollatzResearch.WordTrace tailWord_50041 prefixEnd_50041 17130056954495965371581 := by
  unfold tailWord_50041
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825145211717478167501977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1216763474478318778334651 1825145211717478167501977)
  ·
    refine ⟨1368858908788108625626483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1825145211717478167501977 1368858908788108625626483)
    ·
      refine ⟨2053288363182162938439725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368858908788108625626483 2053288363182162938439725)
      ·
        refine ⟨769983136193311101914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2053288363182162938439725 769983136193311101914897)
        ·
          refine ⟨577487352144983326436173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769983136193311101914897 577487352144983326436173)
          ·
            refine ⟨216557757054368747413565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577487352144983326436173 216557757054368747413565)
            ·
              refine ⟨81209158895388280280087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216557757054368747413565 81209158895388280280087)
              ·
                refine ⟨121813738343082420420131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81209158895388280280087 121813738343082420420131)
                ·
                  refine ⟨182720607514623630630197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121813738343082420420131 182720607514623630630197)
                  ·
                    refine ⟨17130056954495965371581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182720607514623630630197 17130056954495965371581)
                    ·
                      rfl

theorem cell22_50041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_50041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50041 prefixEnd_50041 := by exact prefixLift 50041
  have htrace : WordTrace (prefixWord ++ tailWord_50041) baseStart_50041 baseEnd_50041 := by
    simpa [prefixWord, tailWord_50041, baseEnd_50041] using wordTrace_append hprefix tailTrace_50041
  have hstable : (prefixWord ++ tailWord_50041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50041).length < 2 ^ (prefixWord ++ tailWord_50041).sum := by decide
  have hdescent : baseEnd_50041 < baseStart_50041 := by decide
  rcases family_descends (prefixWord ++ tailWord_50041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50056 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_50056 : Nat := 118140960795 + 50056 * 2 ^ 59
def prefixEnd_50056 : Nat := 4983230072969 + 3 ^ 40 * 50056 * 2
def baseEnd_50056 : Nat := 17135191761040926246535

theorem tailTrace_50056 : CollatzResearch.WordTrace tailWord_50056 prefixEnd_50056 17135191761040926246535 := by
  unfold tailWord_50056
  simp only [CollatzResearch.WordTrace]
  refine ⟨912846153331567864649011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1217128204442090486198681 912846153331567864649011)
  ·
    refine ⟨1369269229997351796973517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912846153331567864649011 1369269229997351796973517)
    ·
      refine ⟨513475961249006923865069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1369269229997351796973517 513475961249006923865069)
      ·
        refine ⟨192553485468377596449401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513475961249006923865069 192553485468377596449401)
        ·
          refine ⟨144415114101283197337051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192553485468377596449401 144415114101283197337051)
          ·
            refine ⟨216622671151924796005577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144415114101283197337051 216622671151924796005577)
            ·
              refine ⟨162467003363943597004183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216622671151924796005577 162467003363943597004183)
              ·
                refine ⟨243700505045915395506275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162467003363943597004183 243700505045915395506275)
                ·
                  refine ⟨365550757568873093259413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243700505045915395506275 365550757568873093259413)
                  ·
                    refine ⟨17135191761040926246535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 365550757568873093259413 17135191761040926246535)
                    ·
                      rfl

theorem cell22_50056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_50056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50056 prefixEnd_50056 := by exact prefixLift 50056
  have htrace : WordTrace (prefixWord ++ tailWord_50056) baseStart_50056 baseEnd_50056 := by
    simpa [prefixWord, tailWord_50056, baseEnd_50056] using wordTrace_append hprefix tailTrace_50056
  have hstable : (prefixWord ++ tailWord_50056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50056).length < 2 ^ (prefixWord ++ tailWord_50056).sum := by decide
  have hdescent : baseEnd_50056 < baseStart_50056 := by decide
  rcases family_descends (prefixWord ++ tailWord_50056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50058 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_50058 : Nat := 118140960795 + 50058 * 2 ^ 59
def prefixEnd_50058 : Nat := 4983230072969 + 3 ^ 40 * 50058 * 2
def baseEnd_50058 : Nat := 17135876401913587696529

theorem tailTrace_50058 : CollatzResearch.WordTrace tailWord_50058 prefixEnd_50058 17135876401913587696529 := by
  unfold tailWord_50058
  simp only [CollatzResearch.WordTrace]
  refine ⟨456441313163972517717707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1217176835103926713913885 456441313163972517717707)
  ·
    refine ⟨684661969745958776576561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456441313163972517717707 684661969745958776576561)
    ·
      refine ⟨513496477309469082432421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 684661969745958776576561 513496477309469082432421)
      ·
        refine ⟨96280589495525452956079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513496477309469082432421 96280589495525452956079)
        ·
          refine ⟨144420884243288179434119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96280589495525452956079 144420884243288179434119)
          ·
            refine ⟨216631326364932269151179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144420884243288179434119 216631326364932269151179)
            ·
              refine ⟨324946989547398403726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216631326364932269151179 324946989547398403726769)
              ·
                refine ⟨243710242160548802795077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324946989547398403726769 243710242160548802795077)
                ·
                  refine ⟨45695670405102900524077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243710242160548802795077 45695670405102900524077)
                  ·
                    refine ⟨17135876401913587696529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45695670405102900524077 17135876401913587696529)
                    ·
                      rfl

theorem cell22_50058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_50058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50058 prefixEnd_50058 := by exact prefixLift 50058
  have htrace : WordTrace (prefixWord ++ tailWord_50058) baseStart_50058 baseEnd_50058 := by
    simpa [prefixWord, tailWord_50058, baseEnd_50058] using wordTrace_append hprefix tailTrace_50058
  have hstable : (prefixWord ++ tailWord_50058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50058).length < 2 ^ (prefixWord ++ tailWord_50058).sum := by decide
  have hdescent : baseEnd_50058 < baseStart_50058 := by decide
  rcases family_descends (prefixWord ++ tailWord_50058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50099 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 9]
def baseStart_50099 : Nat := 118140960795 + 50099 * 2 ^ 59
def prefixEnd_50099 : Nat := 4983230072969 + 3 ^ 40 * 50099 * 2
def baseEnd_50099 : Nat := 5716637179934382473801

theorem tailTrace_50099 : CollatzResearch.WordTrace tailWord_50099 prefixEnd_50099 5716637179934382473801 := by
  unfold tailWord_50099
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827260645507354073113351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1218173763671569382075567 1827260645507354073113351)
  ·
    refine ⟨2740890968261031109670027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827260645507354073113351 2740890968261031109670027)
    ·
      refine ⟨4111336452391546664505041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740890968261031109670027 4111336452391546664505041)
      ·
        refine ⟨3083502339293659998378781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4111336452391546664505041 3083502339293659998378781)
        ·
          refine ⟨1156313377235122499392043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3083502339293659998378781 1156313377235122499392043)
          ·
            refine ⟨1734470065852683749088065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156313377235122499392043 1734470065852683749088065)
            ·
              refine ⟨1300852549389512811816049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734470065852683749088065 1300852549389512811816049)
              ·
                refine ⟨975639412042134608862037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300852549389512811816049 975639412042134608862037)
                ·
                  refine ⟨5716637179934382473801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 975639412042134608862037 5716637179934382473801)
                  ·
                    rfl

theorem cell22_50099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_50099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50099 prefixEnd_50099 := by exact prefixLift 50099
  have htrace : WordTrace (prefixWord ++ tailWord_50099) baseStart_50099 baseEnd_50099 := by
    simpa [prefixWord, tailWord_50099, baseEnd_50099] using wordTrace_append hprefix tailTrace_50099
  have hstable : (prefixWord ++ tailWord_50099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50099).length < 2 ^ (prefixWord ++ tailWord_50099).sum := by decide
  have hdescent : baseEnd_50099 < baseStart_50099 := by decide
  rcases family_descends (prefixWord ++ tailWord_50099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50137 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_50137 : Nat := 118140960795 + 50137 * 2 ^ 59
def prefixEnd_50137 : Nat := 4983230072969 + 3 ^ 40 * 50137 * 2
def baseEnd_50137 : Nat := 17162919716383714971287

theorem tailTrace_50137 : CollatzResearch.WordTrace tailWord_50137 prefixEnd_50137 17162919716383714971287 := by
  unfold tailWord_50137
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828646619369686562996665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1219097746246457708664443 1828646619369686562996665)
  ·
    refine ⟨1371484964527264922247499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828646619369686562996665 1371484964527264922247499)
    ·
      refine ⟨2057227446790897383371249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371484964527264922247499 2057227446790897383371249)
      ·
        refine ⟨1542920585093173037528437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2057227446790897383371249 1542920585093173037528437)
        ·
          refine ⟨144648804852484972268291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1542920585093173037528437 144648804852484972268291)
          ·
            refine ⟨216973207278727458402437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144648804852484972268291 216973207278727458402437)
            ·
              refine ⟨40682476364761398450457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216973207278727458402437 40682476364761398450457)
              ·
                refine ⟨30511857273571048837843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40682476364761398450457 30511857273571048837843)
                ·
                  refine ⟨45767785910356573256765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30511857273571048837843 45767785910356573256765)
                  ·
                    refine ⟨17162919716383714971287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45767785910356573256765 17162919716383714971287)
                    ·
                      rfl

theorem cell22_50137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_50137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50137 prefixEnd_50137 := by exact prefixLift 50137
  have htrace : WordTrace (prefixWord ++ tailWord_50137) baseStart_50137 baseEnd_50137 := by
    simpa [prefixWord, tailWord_50137, baseEnd_50137] using wordTrace_append hprefix tailTrace_50137
  have hstable : (prefixWord ++ tailWord_50137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50137).length < 2 ^ (prefixWord ++ tailWord_50137).sum := by decide
  have hdescent : baseEnd_50137 < baseStart_50137 := by decide
  rcases family_descends (prefixWord ++ tailWord_50137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50161 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 8]
def baseStart_50161 : Nat := 118140960795 + 50161 * 2 ^ 59
def prefixEnd_50161 : Nat := 4983230072969 + 3 ^ 40 * 50161 * 2
def baseEnd_50161 : Nat := 5723711802285217457071

theorem tailTrace_50161 : CollatzResearch.WordTrace tailWord_50161 prefixEnd_50161 5723711802285217457071 := by
  unfold tailWord_50161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829521971282738661870337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1219681314188492441246891 1829521971282738661870337)
  ·
    refine ⟨1372141478462053996402753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1829521971282738661870337 1372141478462053996402753)
    ·
      refine ⟨1029106108846540497302065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372141478462053996402753 1029106108846540497302065)
      ·
        refine ⟨771829581634905372976549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1029106108846540497302065 771829581634905372976549)
        ·
          refine ⟨144718046556544757433103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 771829581634905372976549 144718046556544757433103)
          ·
            refine ⟨217077069834817136149655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144718046556544757433103 217077069834817136149655)
            ·
              refine ⟨325615604752225704224483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217077069834817136149655 325615604752225704224483)
              ·
                refine ⟨488423407128338556336725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325615604752225704224483 488423407128338556336725)
                ·
                  refine ⟨5723711802285217457071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 488423407128338556336725 5723711802285217457071)
                  ·
                    rfl

theorem cell22_50161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_50161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50161 prefixEnd_50161 := by exact prefixLift 50161
  have htrace : WordTrace (prefixWord ++ tailWord_50161) baseStart_50161 baseEnd_50161 := by
    simpa [prefixWord, tailWord_50161, baseEnd_50161] using wordTrace_append hprefix tailTrace_50161
  have hstable : (prefixWord ++ tailWord_50161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50161).length < 2 ^ (prefixWord ++ tailWord_50161).sum := by decide
  have hdescent : baseEnd_50161 < baseStart_50161 := by decide
  rcases family_descends (prefixWord ++ tailWord_50161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50210 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_50210 : Nat := 118140960795 + 50210 * 2 ^ 59
def prefixEnd_50210 : Nat := 4983230072969 + 3 ^ 40 * 50210 * 2
def baseEnd_50210 : Nat := 17187909108235857896063

theorem tailTrace_50210 : CollatzResearch.WordTrace tailWord_50210 prefixEnd_50210 17187909108235857896063 := by
  unfold tailWord_50210
  simp only [CollatzResearch.WordTrace]
  refine ⟨457827287026305007601021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1220872765403480020269389 457827287026305007601021)
  ·
    refine ⟨171685232634864377850383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 457827287026305007601021 171685232634864377850383)
    ·
      refine ⟨257527848952296566775575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171685232634864377850383 257527848952296566775575)
      ·
        refine ⟨386291773428444850163363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257527848952296566775575 386291773428444850163363)
        ·
          refine ⟨579437660142667275245045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386291773428444850163363 579437660142667275245045)
          ·
            refine ⟨54322280638375057054223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 579437660142667275245045 54322280638375057054223)
            ·
              refine ⟨81483420957562585581335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54322280638375057054223 81483420957562585581335)
              ·
                refine ⟨122225131436343878372003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81483420957562585581335 122225131436343878372003)
                ·
                  refine ⟨183337697154515817558005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122225131436343878372003 183337697154515817558005)
                  ·
                    refine ⟨17187909108235857896063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 183337697154515817558005 17187909108235857896063)
                    ·
                      rfl

theorem cell22_50210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_50210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50210 prefixEnd_50210 := by exact prefixLift 50210
  have htrace : WordTrace (prefixWord ++ tailWord_50210) baseStart_50210 baseEnd_50210 := by
    simpa [prefixWord, tailWord_50210, baseEnd_50210] using wordTrace_append hprefix tailTrace_50210
  have hstable : (prefixWord ++ tailWord_50210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50210).length < 2 ^ (prefixWord ++ tailWord_50210).sum := by decide
  have hdescent : baseEnd_50210 < baseStart_50210 := by decide
  rcases family_descends (prefixWord ++ tailWord_50210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50330 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_50330 : Nat := 118140960795 + 50330 * 2 ^ 59
def prefixEnd_50330 : Nat := 4983230072969 + 3 ^ 40 * 50330 * 2
def baseEnd_50330 : Nat := 5742995853531848298565

theorem tailTrace_50330 : CollatzResearch.WordTrace tailWord_50330 prefixEnd_50330 5742995853531848298565 := by
  unfold tailWord_50330
  simp only [CollatzResearch.WordTrace]
  refine ⟨458921476917620131193111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1223790605113653683181629 458921476917620131193111)
  ·
    refine ⟨688382215376430196789667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458921476917620131193111 688382215376430196789667)
    ·
      refine ⟨1032573323064645295184501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688382215376430196789667 1032573323064645295184501)
      ·
        refine ⟨96803749037310496423547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1032573323064645295184501 96803749037310496423547)
        ·
          refine ⟨145205623555965744635321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96803749037310496423547 145205623555965744635321)
          ·
            refine ⟨108904217666974308476491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145205623555965744635321 108904217666974308476491)
            ·
              refine ⟨163356326500461462714737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108904217666974308476491 163356326500461462714737)
              ·
                refine ⟨122517244875346097036053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163356326500461462714737 122517244875346097036053)
                ·
                  refine ⟨5742995853531848298565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122517244875346097036053 5742995853531848298565)
                  ·
                    rfl

theorem cell22_50330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_50330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50330 prefixEnd_50330 := by exact prefixLift 50330
  have htrace : WordTrace (prefixWord ++ tailWord_50330) baseStart_50330 baseEnd_50330 := by
    simpa [prefixWord, tailWord_50330, baseEnd_50330] using wordTrace_append hprefix tailTrace_50330
  have hstable : (prefixWord ++ tailWord_50330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50330).length < 2 ^ (prefixWord ++ tailWord_50330).sum := by decide
  have hdescent : baseEnd_50330 < baseStart_50330 := by decide
  rcases family_descends (prefixWord ++ tailWord_50330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50392 : List Nat := [2, 1, 2, 2, 5, 2, 2, 6]
def baseStart_50392 : Nat := 118140960795 + 50392 * 2 ^ 59
def prefixEnd_50392 : Nat := 4983230072969 + 3 ^ 40 * 50392 * 2
def baseEnd_50392 : Nat := 1916690158627561093945

theorem tailTrace_50392 : CollatzResearch.WordTrace tailWord_50392 prefixEnd_50392 1916690158627561093945 := by
  unfold tailWord_50392
  simp only [CollatzResearch.WordTrace]
  refine ⟨918973616722932556764715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1225298155630576742352953 918973616722932556764715)
  ·
    refine ⟨1378460425084398835147073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918973616722932556764715 1378460425084398835147073)
    ·
      refine ⟨1033845318813299126360305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1378460425084398835147073 1033845318813299126360305)
      ·
        refine ⟨775383989109974344770229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033845318813299126360305 775383989109974344770229)
        ·
          refine ⟨72692248979060094822209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 775383989109974344770229 72692248979060094822209)
          ·
            refine ⟨54519186734295071116657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72692248979060094822209 54519186734295071116657)
            ·
              refine ⟨40889390050721303337493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54519186734295071116657 40889390050721303337493)
              ·
                refine ⟨1916690158627561093945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40889390050721303337493 1916690158627561093945)
                ·
                  rfl

theorem cell22_50392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_50392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50392 prefixEnd_50392 := by exact prefixLift 50392
  have htrace : WordTrace (prefixWord ++ tailWord_50392) baseStart_50392 baseEnd_50392 := by
    simpa [prefixWord, tailWord_50392, baseEnd_50392] using wordTrace_append hprefix tailTrace_50392
  have hstable : (prefixWord ++ tailWord_50392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50392).length < 2 ^ (prefixWord ++ tailWord_50392).sum := by decide
  have hdescent : baseEnd_50392 < baseStart_50392 := by decide
  rcases family_descends (prefixWord ++ tailWord_50392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50497 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_50497 : Nat := 118140960795 + 50497 * 2 ^ 59
def prefixEnd_50497 : Nat := 4983230072969 + 3 ^ 40 * 50497 * 2
def baseEnd_50497 : Nat := 17286155073462775970183

theorem tailTrace_50497 : CollatzResearch.WordTrace tailWord_50497 prefixEnd_50497 17286155073462775970183 := by
  unfold tailWord_50497
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841776898065468046101745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1227851265376978697401163 1841776898065468046101745)
  ·
    refine ⟨1381332673549101034576309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1841776898065468046101745 1381332673549101034576309)
    ·
      refine ⟨129499938145228221991529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1381332673549101034576309 129499938145228221991529)
      ·
        refine ⟨97124953608921166493647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129499938145228221991529 97124953608921166493647)
        ·
          refine ⟨145687430413381749740471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97124953608921166493647 145687430413381749740471)
          ·
            refine ⟨218531145620072624610707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145687430413381749740471 218531145620072624610707)
            ·
              refine ⟨327796718430108936916061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218531145620072624610707 327796718430108936916061)
              ·
                refine ⟨122923769411290851343523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327796718430108936916061 122923769411290851343523)
                ·
                  refine ⟨184385654116936277015285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122923769411290851343523 184385654116936277015285)
                  ·
                    refine ⟨17286155073462775970183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184385654116936277015285 17286155073462775970183)
                    ·
                      rfl

theorem cell22_50497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_50497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50497 prefixEnd_50497 := by exact prefixLift 50497
  have htrace : WordTrace (prefixWord ++ tailWord_50497) baseStart_50497 baseEnd_50497 := by
    simpa [prefixWord, tailWord_50497, baseEnd_50497] using wordTrace_append hprefix tailTrace_50497
  have hstable : (prefixWord ++ tailWord_50497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50497).length < 2 ^ (prefixWord ++ tailWord_50497).sum := by decide
  have hdescent : baseEnd_50497 < baseStart_50497 := by decide
  rcases family_descends (prefixWord ++ tailWord_50497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50561 : List Nat := [1, 2, 4, 3, 3, 1, 2, 6]
def baseStart_50561 : Nat := 118140960795 + 50561 * 2 ^ 59
def prefixEnd_50561 : Nat := 4983230072969 + 3 ^ 40 * 50561 * 2
def baseEnd_50561 : Nat := 1923118175709771374443

theorem tailTrace_50561 : CollatzResearch.WordTrace tailWord_50561 prefixEnd_50561 1923118175709771374443 := by
  unfold tailWord_50561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844111169833606976431537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1229407446555737984287691 1844111169833606976431537)
  ·
    refine ⟨1383083377375205232323653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1844111169833606976431537 1383083377375205232323653)
    ·
      refine ⟨259328133257850981060685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1383083377375205232323653 259328133257850981060685)
      ·
        refine ⟨97248049971694117897757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259328133257850981060685 97248049971694117897757)
        ·
          refine ⟨36468018739385294211659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97248049971694117897757 36468018739385294211659)
          ·
            refine ⟨54702028109077941317489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36468018739385294211659 54702028109077941317489)
            ·
              refine ⟨41026521081808455988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54702028109077941317489 41026521081808455988117)
              ·
                refine ⟨1923118175709771374443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41026521081808455988117 1923118175709771374443)
                ·
                  rfl

theorem cell22_50561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 6].length) (baseStart_50561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50561 prefixEnd_50561 := by exact prefixLift 50561
  have htrace : WordTrace (prefixWord ++ tailWord_50561) baseStart_50561 baseEnd_50561 := by
    simpa [prefixWord, tailWord_50561, baseEnd_50561] using wordTrace_append hprefix tailTrace_50561
  have hstable : (prefixWord ++ tailWord_50561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50561).length < 2 ^ (prefixWord ++ tailWord_50561).sum := by decide
  have hdescent : baseEnd_50561 < baseStart_50561 := by decide
  rcases family_descends (prefixWord ++ tailWord_50561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50632 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_50632 : Nat := 118140960795 + 50632 * 2 ^ 59
def prefixEnd_50632 : Nat := 4983230072969 + 3 ^ 40 * 50632 * 2
def baseEnd_50632 : Nat := 17332368332367423844769

theorem tailTrace_50632 : CollatzResearch.WordTrace tailWord_50632 prefixEnd_50632 17332368332367423844769 := by
  unfold tailWord_50632
  simp only [CollatzResearch.WordTrace]
  refine ⟨923350376288193051133075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1231133835050924068177433 923350376288193051133075)
  ·
    refine ⟨1385025564432289576699613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 923350376288193051133075 1385025564432289576699613)
    ·
      refine ⟨519384586662108591262355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1385025564432289576699613 519384586662108591262355)
      ·
        refine ⟨779076879993162886893533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519384586662108591262355 779076879993162886893533)
        ·
          refine ⟨292153829997436082585075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779076879993162886893533 292153829997436082585075)
          ·
            refine ⟨438230744996154123877613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292153829997436082585075 438230744996154123877613)
            ·
              refine ⟨164336529373557796454105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 438230744996154123877613 164336529373557796454105)
              ·
                refine ⟨123252397030168347340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164336529373557796454105 123252397030168347340579)
                ·
                  refine ⟨184878595545252521010869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123252397030168347340579 184878595545252521010869)
                  ·
                    refine ⟨17332368332367423844769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184878595545252521010869 17332368332367423844769)
                    ·
                      rfl

theorem cell22_50632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_50632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50632 prefixEnd_50632 := by exact prefixLift 50632
  have htrace : WordTrace (prefixWord ++ tailWord_50632) baseStart_50632 baseEnd_50632 := by
    simpa [prefixWord, tailWord_50632, baseEnd_50632] using wordTrace_append hprefix tailTrace_50632
  have hstable : (prefixWord ++ tailWord_50632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50632).length < 2 ^ (prefixWord ++ tailWord_50632).sum := by decide
  have hdescent : baseEnd_50632 < baseStart_50632 := by decide
  rcases family_descends (prefixWord ++ tailWord_50632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50636 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_50636 : Nat := 118140960795 + 50636 * 2 ^ 59
def prefixEnd_50636 : Nat := 4983230072969 + 3 ^ 40 * 50636 * 2
def baseEnd_50636 : Nat := 17333737614112746744757

theorem tailTrace_50636 : CollatzResearch.WordTrace tailWord_50636 prefixEnd_50636 17333737614112746744757 := by
  unfold tailWord_50636
  simp only [CollatzResearch.WordTrace]
  refine ⟨923423322280947392705881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1231231096374596523607841 923423322280947392705881)
  ·
    refine ⟨692567491710710544529411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923423322280947392705881 692567491710710544529411)
    ·
      refine ⟨1038851237566065816794117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692567491710710544529411 1038851237566065816794117)
      ·
        refine ⟨194784607043637340648897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1038851237566065816794117 194784607043637340648897)
        ·
          refine ⟨146088455282728005486673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194784607043637340648897 146088455282728005486673)
          ·
            refine ⟨109566341462046004115005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146088455282728005486673 109566341462046004115005)
            ·
              refine ⟨41087378048267251543127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109566341462046004115005 41087378048267251543127)
              ·
                refine ⟨61631067072400877314691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41087378048267251543127 61631067072400877314691)
                ·
                  refine ⟨92446600608601315972037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61631067072400877314691 92446600608601315972037)
                  ·
                    refine ⟨17333737614112746744757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92446600608601315972037 17333737614112746744757)
                    ·
                      rfl

theorem cell22_50636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_50636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50636 prefixEnd_50636 := by exact prefixLift 50636
  have htrace : WordTrace (prefixWord ++ tailWord_50636) baseStart_50636 baseEnd_50636 := by
    simpa [prefixWord, tailWord_50636, baseEnd_50636] using wordTrace_append hprefix tailTrace_50636
  have hstable : (prefixWord ++ tailWord_50636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50636).length < 2 ^ (prefixWord ++ tailWord_50636).sum := by decide
  have hdescent : baseEnd_50636 < baseStart_50636 := by decide
  rcases family_descends (prefixWord ++ tailWord_50636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50649 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_50649 : Nat := 118140960795 + 50649 * 2 ^ 59
def prefixEnd_50649 : Nat := 4983230072969 + 3 ^ 40 * 50649 * 2
def baseEnd_50649 : Nat := 17338187779785046169717

theorem tailTrace_50649 : CollatzResearch.WordTrace tailWord_50649 prefixEnd_50649 17338187779785046169717 := by
  unfold tailWord_50649
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847320793514798005635001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1231547195676532003756667 1847320793514798005635001)
  ·
    refine ⟨1385490595136098504226251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1847320793514798005635001 1385490595136098504226251)
    ·
      refine ⟨2078235892704147756339377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385490595136098504226251 2078235892704147756339377)
      ·
        refine ⟨1558676919528110817254533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078235892704147756339377 1558676919528110817254533)
        ·
          refine ⟨292251922411520778235225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1558676919528110817254533 292251922411520778235225)
          ·
            refine ⟨219188941808640583676419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292251922411520778235225 219188941808640583676419)
            ·
              refine ⟨328783412712960875514629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219188941808640583676419 328783412712960875514629)
              ·
                refine ⟨61646889883680164158993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328783412712960875514629 61646889883680164158993)
                ·
                  refine ⟨46235167412760123119245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61646889883680164158993 46235167412760123119245)
                  ·
                    refine ⟨17338187779785046169717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46235167412760123119245 17338187779785046169717)
                    ·
                      rfl

theorem cell22_50649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_50649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50649 prefixEnd_50649 := by exact prefixLift 50649
  have htrace : WordTrace (prefixWord ++ tailWord_50649) baseStart_50649 baseEnd_50649 := by
    simpa [prefixWord, tailWord_50649, baseEnd_50649] using wordTrace_append hprefix tailTrace_50649
  have hstable : (prefixWord ++ tailWord_50649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50649).length < 2 ^ (prefixWord ++ tailWord_50649).sum := by decide
  have hdescent : baseEnd_50649 < baseStart_50649 := by decide
  rcases family_descends (prefixWord ++ tailWord_50649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50707 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 7]
def baseStart_50707 : Nat := 118140960795 + 50707 * 2 ^ 59
def prefixEnd_50707 : Nat := 4983230072969 + 3 ^ 40 * 50707 * 2
def baseEnd_50707 : Nat := 5786014121697409406513

theorem tailTrace_50707 : CollatzResearch.WordTrace tailWord_50707 prefixEnd_50707 5786014121697409406513 := by
  unfold tailWord_50707
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849436227304673911246375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1232957484869782607497583 1849436227304673911246375)
  ·
    refine ⟨2774154340957010866869563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1849436227304673911246375 2774154340957010866869563)
    ·
      refine ⟨4161231511435516300304345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774154340957010866869563 4161231511435516300304345)
      ·
        refine ⟨3120923633576637225228259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4161231511435516300304345 3120923633576637225228259)
        ·
          refine ⟨4681385450364955837842389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120923633576637225228259 4681385450364955837842389)
          ·
            refine ⟨109719971492928652449431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4681385450364955837842389 109719971492928652449431)
            ·
              refine ⟨164579957239392978674147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109719971492928652449431 164579957239392978674147)
              ·
                refine ⟨246869935859089468011221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164579957239392978674147 246869935859089468011221)
                ·
                  refine ⟨5786014121697409406513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 246869935859089468011221 5786014121697409406513)
                  ·
                    rfl

theorem cell22_50707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_50707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50707 prefixEnd_50707 := by exact prefixLift 50707
  have htrace : WordTrace (prefixWord ++ tailWord_50707) baseStart_50707 baseEnd_50707 := by
    simpa [prefixWord, tailWord_50707, baseEnd_50707] using wordTrace_append hprefix tailTrace_50707
  have hstable : (prefixWord ++ tailWord_50707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50707).length < 2 ^ (prefixWord ++ tailWord_50707).sum := by decide
  have hdescent : baseEnd_50707 < baseStart_50707 := by decide
  rcases family_descends (prefixWord ++ tailWord_50707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50820 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 4]
def baseStart_50820 : Nat := 118140960795 + 50820 * 2 ^ 59
def prefixEnd_50820 : Nat := 4983230072969 + 3 ^ 40 * 50820 * 2
def baseEnd_50820 : Nat := 5798908191465866714731

theorem tailTrace_50820 : CollatzResearch.WordTrace tailWord_50820 prefixEnd_50820 5798908191465866714731 := by
  unfold tailWord_50820
  simp only [CollatzResearch.WordTrace]
  refine ⟨926778837947647105054957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1235705117263529473406609 926778837947647105054957)
  ·
    refine ⟨347542064230367664395609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 926778837947647105054957 347542064230367664395609)
    ·
      refine ⟨260656548172775748296707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347542064230367664395609 260656548172775748296707)
      ·
        refine ⟨390984822259163622445061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260656548172775748296707 390984822259163622445061)
        ·
          refine ⟨73309654173593179208449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 390984822259163622445061 73309654173593179208449)
          ·
            refine ⟨54982240630194884406337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73309654173593179208449 54982240630194884406337)
            ·
              refine ⟨41236680472646163304753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54982240630194884406337 41236680472646163304753)
              ·
                refine ⟨30927510354484622478565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41236680472646163304753 30927510354484622478565)
                ·
                  refine ⟨5798908191465866714731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30927510354484622478565 5798908191465866714731)
                  ·
                    rfl

theorem cell22_50820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_50820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50820 prefixEnd_50820 := by exact prefixLift 50820
  have htrace : WordTrace (prefixWord ++ tailWord_50820) baseStart_50820 baseEnd_50820 := by
    simpa [prefixWord, tailWord_50820, baseEnd_50820] using wordTrace_append hprefix tailTrace_50820
  have hstable : (prefixWord ++ tailWord_50820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50820).length < 2 ^ (prefixWord ++ tailWord_50820).sum := by decide
  have hdescent : baseEnd_50820 < baseStart_50820 := by decide
  rcases family_descends (prefixWord ++ tailWord_50820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50827 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_50827 : Nat := 118140960795 + 50827 * 2 ^ 59
def prefixEnd_50827 : Nat := 4983230072969 + 3 ^ 40 * 50827 * 2
def baseEnd_50827 : Nat := 17399120817451915219171

theorem tailTrace_50827 : CollatzResearch.WordTrace tailWord_50827 prefixEnd_50827 17399120817451915219171 := by
  unfold tailWord_50827
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853812986869934405614735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1235875324579956270409823 1853812986869934405614735)
  ·
    refine ⟨2780719480304901608422103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853812986869934405614735 2780719480304901608422103)
    ·
      refine ⟨4171079220457352412633155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780719480304901608422103 4171079220457352412633155)
      ·
        refine ⟨6256618830686028618949733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171079220457352412633155 6256618830686028618949733)
        ·
          refine ⟨1173116030753630366053075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6256618830686028618949733 1173116030753630366053075)
          ·
            refine ⟨1759674046130445549079613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173116030753630366053075 1759674046130445549079613)
            ·
              refine ⟨659877767298917080904855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1759674046130445549079613 659877767298917080904855)
              ·
                refine ⟨989816650948375621357283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659877767298917080904855 989816650948375621357283)
                ·
                  refine ⟨1484724976422563432035925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989816650948375621357283 1484724976422563432035925)
                  ·
                    refine ⟨17399120817451915219171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1484724976422563432035925 17399120817451915219171)
                    ·
                      rfl

theorem cell22_50827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_50827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50827 prefixEnd_50827 := by exact prefixLift 50827
  have htrace : WordTrace (prefixWord ++ tailWord_50827) baseStart_50827 baseEnd_50827 := by
    simpa [prefixWord, tailWord_50827, baseEnd_50827] using wordTrace_append hprefix tailTrace_50827
  have hstable : (prefixWord ++ tailWord_50827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50827).length < 2 ^ (prefixWord ++ tailWord_50827).sum := by decide
  have hdescent : baseEnd_50827 < baseStart_50827 := by decide
  rcases family_descends (prefixWord ++ tailWord_50827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50850 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_50850 : Nat := 118140960795 + 50850 * 2 ^ 59
def prefixEnd_50850 : Nat := 4983230072969 + 3 ^ 40 * 50850 * 2
def baseEnd_50850 : Nat := 17406994187487521894101

theorem tailTrace_50850 : CollatzResearch.WordTrace tailWord_50850 prefixEnd_50850 17406994187487521894101 := by
  unfold tailWord_50850
  simp only [CollatzResearch.WordTrace]
  refine ⟨463662966446652333425501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1236434577191072889134669 463662966446652333425501)
  ·
    refine ⟨173873612417494625034563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 463662966446652333425501 173873612417494625034563)
    ·
      refine ⟨260810418626241937551845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173873612417494625034563 260810418626241937551845)
      ·
        refine ⟨48901953492420363290971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260810418626241937551845 48901953492420363290971)
        ·
          refine ⟨73352930238630544936457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48901953492420363290971 73352930238630544936457)
          ·
            refine ⟨55014697678972908702343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73352930238630544936457 55014697678972908702343)
            ·
              refine ⟨82522046518459363053515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55014697678972908702343 82522046518459363053515)
              ·
                refine ⟨123783069777689044580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82522046518459363053515 123783069777689044580273)
                ·
                  refine ⟨92837302333266783435205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123783069777689044580273 92837302333266783435205)
                  ·
                    refine ⟨17406994187487521894101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92837302333266783435205 17406994187487521894101)
                    ·
                      rfl

theorem cell22_50850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_50850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50850 prefixEnd_50850 := by exact prefixLift 50850
  have htrace : WordTrace (prefixWord ++ tailWord_50850) baseStart_50850 baseEnd_50850 := by
    simpa [prefixWord, tailWord_50850, baseEnd_50850] using wordTrace_append hprefix tailTrace_50850
  have hstable : (prefixWord ++ tailWord_50850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50850).length < 2 ^ (prefixWord ++ tailWord_50850).sum := by decide
  have hdescent : baseEnd_50850 < baseStart_50850 := by decide
  rcases family_descends (prefixWord ++ tailWord_50850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50863 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 1, 3]
def baseStart_50863 : Nat := 118140960795 + 50863 * 2 ^ 59
def prefixEnd_50863 : Nat := 4983230072969 + 3 ^ 40 * 50863 * 2
def baseEnd_50863 : Nat := 17411444353159821319061

theorem tailTrace_50863 : CollatzResearch.WordTrace tailWord_50863 prefixEnd_50863 17411444353159821319061 := by
  unfold tailWord_50863
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855126014739512553925243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1236750676493008369283495 1855126014739512553925243)
  ·
    refine ⟨2782689022109268830887865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855126014739512553925243 2782689022109268830887865)
    ·
      refine ⟨2087016766581951623165899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2782689022109268830887865 2087016766581951623165899)
      ·
        refine ⟨3130525149872927434748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087016766581951623165899 3130525149872927434748849)
        ·
          refine ⟨2347893862404695576061637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130525149872927434748849 2347893862404695576061637)
          ·
            refine ⟨440230099200880420511557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2347893862404695576061637 440230099200880420511557)
            ·
              refine ⟨82543143600165078845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440230099200880420511557 82543143600165078845917)
              ·
                refine ⟨30953678850061904567219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82543143600165078845917 30953678850061904567219)
                ·
                  refine ⟨46430518275092856850829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30953678850061904567219 46430518275092856850829)
                  ·
                    refine ⟨17411444353159821319061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46430518275092856850829 17411444353159821319061)
                    ·
                      rfl

theorem cell22_50863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_50863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50863 prefixEnd_50863 := by exact prefixLift 50863
  have htrace : WordTrace (prefixWord ++ tailWord_50863) baseStart_50863 baseEnd_50863 := by
    simpa [prefixWord, tailWord_50863, baseEnd_50863] using wordTrace_append hprefix tailTrace_50863
  have hstable : (prefixWord ++ tailWord_50863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50863).length < 2 ^ (prefixWord ++ tailWord_50863).sum := by decide
  have hdescent : baseEnd_50863 < baseStart_50863 := by decide
  rcases family_descends (prefixWord ++ tailWord_50863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50874 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_50874 : Nat := 118140960795 + 50874 * 2 ^ 59
def prefixEnd_50874 : Nat := 4983230072969 + 3 ^ 40 * 50874 * 2
def baseEnd_50874 : Nat := 17415209877959459294027

theorem tailTrace_50874 : CollatzResearch.WordTrace tailWord_50874 prefixEnd_50874 17415209877959459294027 := by
  unfold tailWord_50874
  simp only [CollatzResearch.WordTrace]
  refine ⟨463881804424915358143919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1237018145133107621717117 463881804424915358143919)
  ·
    refine ⟨695822706637373037215879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463881804424915358143919 695822706637373037215879)
    ·
      refine ⟨1043734059956059555823819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695822706637373037215879 1043734059956059555823819)
      ·
        refine ⟨1565601089934089333735729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043734059956059555823819 1565601089934089333735729)
        ·
          refine ⟨1174200817450567000301797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565601089934089333735729 1174200817450567000301797)
          ·
            refine ⟨220162653271981312556587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1174200817450567000301797 220162653271981312556587)
            ·
              refine ⟨330243979907971968834881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220162653271981312556587 330243979907971968834881)
              ·
                refine ⟨247682984930978976626161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330243979907971968834881 247682984930978976626161)
                ·
                  refine ⟨185762238698234232469621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247682984930978976626161 185762238698234232469621)
                  ·
                    refine ⟨17415209877959459294027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185762238698234232469621 17415209877959459294027)
                    ·
                      rfl

theorem cell22_50874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_50874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50874 prefixEnd_50874 := by exact prefixLift 50874
  have htrace : WordTrace (prefixWord ++ tailWord_50874) baseStart_50874 baseEnd_50874 := by
    simpa [prefixWord, tailWord_50874, baseEnd_50874] using wordTrace_append hprefix tailTrace_50874
  have hstable : (prefixWord ++ tailWord_50874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50874).length < 2 ^ (prefixWord ++ tailWord_50874).sum := by decide
  have hdescent : baseEnd_50874 < baseStart_50874 := by decide
  rcases family_descends (prefixWord ++ tailWord_50874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50876 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_50876 : Nat := 118140960795 + 50876 * 2 ^ 59
def prefixEnd_50876 : Nat := 4983230072969 + 3 ^ 40 * 50876 * 2
def baseEnd_50876 : Nat := 5805298172944040248007

theorem tailTrace_50876 : CollatzResearch.WordTrace tailWord_50876 prefixEnd_50876 5805298172944040248007 := by
  unfold tailWord_50876
  simp only [CollatzResearch.WordTrace]
  refine ⟨927800081846207887074241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1237066775794943849432321 927800081846207887074241)
  ·
    refine ⟨695850061384655915305681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 927800081846207887074241 695850061384655915305681)
    ·
      refine ⟨521887546038491936479261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 695850061384655915305681 521887546038491936479261)
      ·
        refine ⟨195707829764434476179723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521887546038491936479261 195707829764434476179723)
        ·
          refine ⟨293561744646651714269585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195707829764434476179723 293561744646651714269585)
          ·
            refine ⟨220171308484988785702189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293561744646651714269585 220171308484988785702189)
            ·
              refine ⟨82564240681870794638321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220171308484988785702189 82564240681870794638321)
              ·
                refine ⟨61923180511403095978741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82564240681870794638321 61923180511403095978741)
                ·
                  refine ⟨5805298172944040248007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61923180511403095978741 5805298172944040248007)
                  ·
                    rfl

theorem cell22_50876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_50876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50876 prefixEnd_50876 := by exact prefixLift 50876
  have htrace : WordTrace (prefixWord ++ tailWord_50876) baseStart_50876 baseEnd_50876 := by
    simpa [prefixWord, tailWord_50876, baseEnd_50876] using wordTrace_append hprefix tailTrace_50876
  have hstable : (prefixWord ++ tailWord_50876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50876).length < 2 ^ (prefixWord ++ tailWord_50876).sum := by decide
  have hdescent : baseEnd_50876 < baseStart_50876 := by decide
  rcases family_descends (prefixWord ++ tailWord_50876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50904 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 6]
def baseStart_50904 : Nat := 118140960795 + 50904 * 2 ^ 59
def prefixEnd_50904 : Nat := 4983230072969 + 3 ^ 40 * 50904 * 2
def baseEnd_50904 : Nat := 5808493163683127014645

theorem tailTrace_50904 : CollatzResearch.WordTrace tailWord_50904 prefixEnd_50904 5808493163683127014645 := by
  unfold tailWord_50904
  simp only [CollatzResearch.WordTrace]
  refine ⟨928310703795488278083883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1237747605060651037445177 928310703795488278083883)
  ·
    refine ⟨1392466055693232417125825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 928310703795488278083883 1392466055693232417125825)
    ·
      refine ⟨1044349541769924312844369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392466055693232417125825 1044349541769924312844369)
      ·
        refine ⟨783262156327443234633277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044349541769924312844369 783262156327443234633277)
        ·
          refine ⟨293723308622791212987479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 783262156327443234633277 293723308622791212987479)
          ·
            refine ⟨440584962934186819481219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293723308622791212987479 440584962934186819481219)
            ·
              refine ⟨660877444401280229221829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440584962934186819481219 660877444401280229221829)
              ·
                refine ⟨123914520825240042979093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660877444401280229221829 123914520825240042979093)
                ·
                  refine ⟨5808493163683127014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123914520825240042979093 5808493163683127014645)
                  ·
                    rfl

theorem cell22_50904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_50904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50904 prefixEnd_50904 := by exact prefixLift 50904
  have htrace : WordTrace (prefixWord ++ tailWord_50904) baseStart_50904 baseEnd_50904 := by
    simpa [prefixWord, tailWord_50904, baseEnd_50904] using wordTrace_append hprefix tailTrace_50904
  have hstable : (prefixWord ++ tailWord_50904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50904).length < 2 ^ (prefixWord ++ tailWord_50904).sum := by decide
  have hdescent : baseEnd_50904 < baseStart_50904 := by decide
  rcases family_descends (prefixWord ++ tailWord_50904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50906 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_50906 : Nat := 118140960795 + 50906 * 2 ^ 59
def prefixEnd_50906 : Nat := 4983230072969 + 3 ^ 40 * 50906 * 2
def baseEnd_50906 : Nat := 17426164131922042493929

theorem tailTrace_50906 : CollatzResearch.WordTrace tailWord_50906 prefixEnd_50906 17426164131922042493929 := by
  unfold tailWord_50906
  simp only [CollatzResearch.WordTrace]
  refine ⟨464173588395932724435143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1237796235722487265160381 464173588395932724435143)
  ·
    refine ⟨696260382593899086652715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 464173588395932724435143 696260382593899086652715)
    ·
      refine ⟨1044390573890848629979073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696260382593899086652715 1044390573890848629979073)
      ·
        refine ⟨783292930418136472484305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044390573890848629979073 783292930418136472484305)
        ·
          refine ⟨587469697813602354363229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783292930418136472484305 587469697813602354363229)
          ·
            refine ⟨220301136680100882886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587469697813602354363229 220301136680100882886211)
            ·
              refine ⟨330451705020151324329317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220301136680100882886211 330451705020151324329317)
              ·
                refine ⟨61959694691278373311747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330451705020151324329317 61959694691278373311747)
                ·
                  refine ⟨92939542036917559967621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61959694691278373311747 92939542036917559967621)
                  ·
                    refine ⟨17426164131922042493929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92939542036917559967621 17426164131922042493929)
                    ·
                      rfl

theorem cell22_50906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_50906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50906 prefixEnd_50906 := by exact prefixLift 50906
  have htrace : WordTrace (prefixWord ++ tailWord_50906) baseStart_50906 baseEnd_50906 := by
    simpa [prefixWord, tailWord_50906, baseEnd_50906] using wordTrace_append hprefix tailTrace_50906
  have hstable : (prefixWord ++ tailWord_50906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50906).length < 2 ^ (prefixWord ++ tailWord_50906).sum := by decide
  have hdescent : baseEnd_50906 < baseStart_50906 := by decide
  rcases family_descends (prefixWord ++ tailWord_50906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50974 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_50974 : Nat := 118140960795 + 50974 * 2 ^ 59
def prefixEnd_50974 : Nat := 4983230072969 + 3 ^ 40 * 50974 * 2
def baseEnd_50974 : Nat := 17449441921592531793721

theorem tailTrace_50974 : CollatzResearch.WordTrace tailWord_50974 prefixEnd_50974 17449441921592531793721 := by
  unfold tailWord_50974
  simp only [CollatzResearch.WordTrace]
  refine ⟨232396814667172313901997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1239449678224919007477317 232396814667172313901997)
  ·
    refine ⟨87148805500189617713249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 232396814667172313901997 87148805500189617713249)
    ·
      refine ⟨65361604125142213284937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87148805500189617713249 65361604125142213284937)
      ·
        refine ⟨49021203093856659963703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65361604125142213284937 49021203093856659963703)
        ·
          refine ⟨73531804640784989945555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49021203093856659963703 73531804640784989945555)
          ·
            refine ⟨110297706961177484918333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73531804640784989945555 110297706961177484918333)
            ·
              refine ⟨41361640110441556844375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110297706961177484918333 41361640110441556844375)
              ·
                refine ⟨62042460165662335266563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41361640110441556844375 62042460165662335266563)
                ·
                  refine ⟨93063690248493502899845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62042460165662335266563 93063690248493502899845)
                  ·
                    refine ⟨17449441921592531793721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93063690248493502899845 17449441921592531793721)
                    ·
                      rfl

theorem cell22_50974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_50974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_50974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_50974 prefixEnd_50974 := by exact prefixLift 50974
  have htrace : WordTrace (prefixWord ++ tailWord_50974) baseStart_50974 baseEnd_50974 := by
    simpa [prefixWord, tailWord_50974, baseEnd_50974] using wordTrace_append hprefix tailTrace_50974
  have hstable : (prefixWord ++ tailWord_50974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50974).length < 2 ^ (prefixWord ++ tailWord_50974).sum := by decide
  have hdescent : baseEnd_50974 < baseStart_50974 := by decide
  rcases family_descends (prefixWord ++ tailWord_50974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51011 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 5]
def baseStart_51011 : Nat := 118140960795 + 51011 * 2 ^ 59
def prefixEnd_51011 : Nat := 4983230072969 + 3 ^ 40 * 51011 * 2
def baseEnd_51011 : Nat := 5820702592578922872869

theorem tailTrace_51011 : CollatzResearch.WordTrace tailWord_51011 prefixEnd_51011 5820702592578922872869 := by
  unfold tailWord_51011
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860524018203333830312887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1240349345468889220208591 1860524018203333830312887)
  ·
    refine ⟨2790786027305000745469331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860524018203333830312887 2790786027305000745469331)
    ·
      refine ⟨4186179040957501118203997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790786027305000745469331 4186179040957501118203997)
      ·
        refine ⟨1569817140359062919326499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4186179040957501118203997 1569817140359062919326499)
        ·
          refine ⟨2354725710538594378989749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569817140359062919326499 2354725710538594378989749)
          ·
            refine ⟨220755535362993223030289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2354725710538594378989749 220755535362993223030289)
            ·
              refine ⟨165566651522244917272717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220755535362993223030289 165566651522244917272717)
              ·
                refine ⟨62087494320841843977269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165566651522244917272717 62087494320841843977269)
                ·
                  refine ⟨5820702592578922872869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62087494320841843977269 5820702592578922872869)
                  ·
                    rfl

theorem cell22_51011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].length) (baseStart_51011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51011 prefixEnd_51011 := by exact prefixLift 51011
  have htrace : WordTrace (prefixWord ++ tailWord_51011) baseStart_51011 baseEnd_51011 := by
    simpa [prefixWord, tailWord_51011, baseEnd_51011] using wordTrace_append hprefix tailTrace_51011
  have hstable : (prefixWord ++ tailWord_51011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51011).length < 2 ^ (prefixWord ++ tailWord_51011).sum := by decide
  have hdescent : baseEnd_51011 < baseStart_51011 := by decide
  rcases family_descends (prefixWord ++ tailWord_51011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51062 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_51062 : Nat := 118140960795 + 51062 * 2 ^ 59
def prefixEnd_51062 : Nat := 4983230072969 + 3 ^ 40 * 51062 * 2
def baseEnd_51062 : Nat := 5826522039996545197817

theorem tailTrace_51062 : CollatzResearch.WordTrace tailWord_51062 prefixEnd_51062 5826522039996545197817 := by
  unfold tailWord_51062
  simp only [CollatzResearch.WordTrace]
  refine ⟨116399008813660596276215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1241589427345713026946293 116399008813660596276215)
  ·
    refine ⟨174598513220490894414323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116399008813660596276215 174598513220490894414323)
    ·
      refine ⟨261897769830736341621485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174598513220490894414323 261897769830736341621485)
      ·
        refine ⟨98211663686526128108057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261897769830736341621485 98211663686526128108057)
        ·
          refine ⟨73658747764894596081043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98211663686526128108057 73658747764894596081043)
          ·
            refine ⟨110488121647341894121565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73658747764894596081043 110488121647341894121565)
            ·
              refine ⟨41433045617753210295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110488121647341894121565 41433045617753210295587)
              ·
                refine ⟨62149568426629815443381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41433045617753210295587 62149568426629815443381)
                ·
                  refine ⟨5826522039996545197817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62149568426629815443381 5826522039996545197817)
                  ·
                    rfl

theorem cell22_51062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_51062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51062 prefixEnd_51062 := by exact prefixLift 51062
  have htrace : WordTrace (prefixWord ++ tailWord_51062) baseStart_51062 baseEnd_51062 := by
    simpa [prefixWord, tailWord_51062, baseEnd_51062] using wordTrace_append hprefix tailTrace_51062
  have hstable : (prefixWord ++ tailWord_51062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51062).length < 2 ^ (prefixWord ++ tailWord_51062).sum := by decide
  have hdescent : baseEnd_51062 < baseStart_51062 := by decide
  rcases family_descends (prefixWord ++ tailWord_51062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51101 : List Nat := [1, 4, 2, 1, 2, 2, 10]
def baseStart_51101 : Nat := 118140960795 + 51101 * 2 ^ 59
def prefixEnd_51101 : Nat := 4983230072969 + 3 ^ 40 * 51101 * 2
def baseEnd_51101 : Nat := 647885800629871624753

theorem tailTrace_51101 : CollatzResearch.WordTrace tailWord_51101 prefixEnd_51101 647885800629871624753 := by
  unfold tailWord_51101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863806587877279201089157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1242537725251519467392771 1863806587877279201089157)
  ·
    refine ⟨349463735226989850204217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1863806587877279201089157 349463735226989850204217)
    ·
      refine ⟨262097801420242387653163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349463735226989850204217 262097801420242387653163)
      ·
        refine ⟨393146702130363581479745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262097801420242387653163 393146702130363581479745)
        ·
          refine ⟨294860026597772686109809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393146702130363581479745 294860026597772686109809)
          ·
            refine ⟨221145019948329514582357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294860026597772686109809 221145019948329514582357)
            ·
              refine ⟨647885800629871624753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 221145019948329514582357 647885800629871624753)
              ·
                rfl

theorem cell22_51101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 10].length) (baseStart_51101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51101 prefixEnd_51101 := by exact prefixLift 51101
  have htrace : WordTrace (prefixWord ++ tailWord_51101) baseStart_51101 baseEnd_51101 := by
    simpa [prefixWord, tailWord_51101, baseEnd_51101] using wordTrace_append hprefix tailTrace_51101
  have hstable : (prefixWord ++ tailWord_51101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51101).length < 2 ^ (prefixWord ++ tailWord_51101).sum := by decide
  have hdescent : baseEnd_51101 < baseStart_51101 := by decide
  rcases family_descends (prefixWord ++ tailWord_51101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51146 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_51146 : Nat := 118140960795 + 51146 * 2 ^ 59
def prefixEnd_51146 : Nat := 4983230072969 + 3 ^ 40 * 51146 * 2
def baseEnd_51146 : Nat := 5836107012213805497731

theorem tailTrace_51146 : CollatzResearch.WordTrace tailWord_51146 prefixEnd_51146 5836107012213805497731 := by
  unfold tailWord_51146
  simp only [CollatzResearch.WordTrace]
  refine ⟨466361968178562971619323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1243631915142834590984861 466361968178562971619323)
  ·
    refine ⟨699542952267844457428985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466361968178562971619323 699542952267844457428985)
    ·
      refine ⟨524657214200883343071739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 699542952267844457428985 524657214200883343071739)
      ·
        refine ⟨786985821301325014607609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524657214200883343071739 786985821301325014607609)
        ·
          refine ⟨590239365975993760955707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786985821301325014607609 590239365975993760955707)
          ·
            refine ⟨885359048963990641433561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590239365975993760955707 885359048963990641433561)
            ·
              refine ⟨664019286722992981075171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885359048963990641433561 664019286722992981075171)
              ·
                refine ⟨996028930084489471612757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664019286722992981075171 996028930084489471612757)
                ·
                  refine ⟨5836107012213805497731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 996028930084489471612757 5836107012213805497731)
                  ·
                    rfl

theorem cell22_51146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_51146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51146 prefixEnd_51146 := by exact prefixLift 51146
  have htrace : WordTrace (prefixWord ++ tailWord_51146) baseStart_51146 baseEnd_51146 := by
    simpa [prefixWord, tailWord_51146, baseEnd_51146] using wordTrace_append hprefix tailTrace_51146
  have hstable : (prefixWord ++ tailWord_51146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51146).length < 2 ^ (prefixWord ++ tailWord_51146).sum := by decide
  have hdescent : baseEnd_51146 < baseStart_51146 := by decide
  rcases family_descends (prefixWord ++ tailWord_51146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51167 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 1, 3]
def baseStart_51167 : Nat := 118140960795 + 51167 * 2 ^ 59
def prefixEnd_51167 : Nat := 4983230072969 + 3 ^ 40 * 51167 * 2
def baseEnd_51167 : Nat := 17515509765804361718129

theorem tailTrace_51167 : CollatzResearch.WordTrace tailWord_51167 prefixEnd_51167 17515509765804361718129 := by
  unfold tailWord_51167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866213805638172472991755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1244142537092114981994503 1866213805638172472991755)
  ·
    refine ⟨2799320708457258709487633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866213805638172472991755 2799320708457258709487633)
    ·
      refine ⟨2099490531342944032115725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799320708457258709487633 2099490531342944032115725)
      ·
        refine ⟨787308949253604012043397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2099490531342944032115725 787308949253604012043397)
        ·
          refine ⟨147620427985050752258137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 787308949253604012043397 147620427985050752258137)
          ·
            refine ⟨110715320988788064193603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147620427985050752258137 110715320988788064193603)
            ·
              refine ⟨166072981483182096290405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110715320988788064193603 166072981483182096290405)
              ·
                refine ⟨31138684028096643054451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166072981483182096290405 31138684028096643054451)
                ·
                  refine ⟨46708026042144964581677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31138684028096643054451 46708026042144964581677)
                  ·
                    refine ⟨17515509765804361718129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46708026042144964581677 17515509765804361718129)
                    ·
                      rfl

theorem cell22_51167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_51167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51167 prefixEnd_51167 := by exact prefixLift 51167
  have htrace : WordTrace (prefixWord ++ tailWord_51167) baseStart_51167 baseEnd_51167 := by
    simpa [prefixWord, tailWord_51167, baseEnd_51167] using wordTrace_append hprefix tailTrace_51167
  have hstable : (prefixWord ++ tailWord_51167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51167).length < 2 ^ (prefixWord ++ tailWord_51167).sum := by decide
  have hdescent : baseEnd_51167 < baseStart_51167 := by decide
  rcases family_descends (prefixWord ++ tailWord_51167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51178 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_51178 : Nat := 118140960795 + 51178 * 2 ^ 59
def prefixEnd_51178 : Nat := 4983230072969 + 3 ^ 40 * 51178 * 2
def baseEnd_51178 : Nat := 17519275290603999693095

theorem tailTrace_51178 : CollatzResearch.WordTrace tailWord_51178 prefixEnd_51178 17519275290603999693095 := by
  unfold tailWord_51178
  simp only [CollatzResearch.WordTrace]
  refine ⟨466653752149580337910547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1244410005732214234428125 466653752149580337910547)
  ·
    refine ⟨699980628224370506865821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466653752149580337910547 699980628224370506865821)
    ·
      refine ⟨262492735584138940074683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 699980628224370506865821 262492735584138940074683)
      ·
        refine ⟨393739103376208410112025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262492735584138940074683 393739103376208410112025)
        ·
          refine ⟨295304327532156307584019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393739103376208410112025 295304327532156307584019)
          ·
            refine ⟨442956491298234461376029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295304327532156307584019 442956491298234461376029)
            ·
              refine ⟨166108684236837923016011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 442956491298234461376029 166108684236837923016011)
              ·
                refine ⟨249163026355256884524017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166108684236837923016011 249163026355256884524017)
                ·
                  refine ⟨186872269766442663393013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249163026355256884524017 186872269766442663393013)
                  ·
                    refine ⟨17519275290603999693095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186872269766442663393013 17519275290603999693095)
                    ·
                      rfl

theorem cell22_51178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_51178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51178 prefixEnd_51178 := by exact prefixLift 51178
  have htrace : WordTrace (prefixWord ++ tailWord_51178) baseStart_51178 baseEnd_51178 := by
    simpa [prefixWord, tailWord_51178, baseEnd_51178] using wordTrace_append hprefix tailTrace_51178
  have hstable : (prefixWord ++ tailWord_51178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51178).length < 2 ^ (prefixWord ++ tailWord_51178).sum := by decide
  have hdescent : baseEnd_51178 < baseStart_51178 := by decide
  rcases family_descends (prefixWord ++ tailWord_51178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51193 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_51193 : Nat := 118140960795 + 51193 * 2 ^ 59
def prefixEnd_51193 : Nat := 4983230072969 + 3 ^ 40 * 51193 * 2
def baseEnd_51193 : Nat := 17524410097148960568049

theorem tailTrace_51193 : CollatzResearch.WordTrace tailWord_51193 prefixEnd_51193 17524410097148960568049 := by
  unfold tailWord_51193
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867162103543978913438233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1244774735695985942292155 1867162103543978913438233)
  ·
    refine ⟨1400371577657984185078675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1867162103543978913438233 1400371577657984185078675)
    ·
      refine ⟨2100557366486976277618013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1400371577657984185078675 2100557366486976277618013)
      ·
        refine ⟨787709012432616104106755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2100557366486976277618013 787709012432616104106755)
        ·
          refine ⟨1181563518648924156160133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787709012432616104106755 1181563518648924156160133)
          ·
            refine ⟨221543159746673279280025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1181563518648924156160133 221543159746673279280025)
            ·
              refine ⟨166157369810004959460019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221543159746673279280025 166157369810004959460019)
              ·
                refine ⟨249236054715007439190029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166157369810004959460019 249236054715007439190029)
                ·
                  refine ⟨93463520518127789696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249236054715007439190029 93463520518127789696261)
                  ·
                    refine ⟨17524410097148960568049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93463520518127789696261 17524410097148960568049)
                    ·
                      rfl

theorem cell22_51193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_51193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51193 prefixEnd_51193 := by exact prefixLift 51193
  have htrace : WordTrace (prefixWord ++ tailWord_51193) baseStart_51193 baseEnd_51193 := by
    simpa [prefixWord, tailWord_51193, baseEnd_51193] using wordTrace_append hprefix tailTrace_51193
  have hstable : (prefixWord ++ tailWord_51193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51193).length < 2 ^ (prefixWord ++ tailWord_51193).sum := by decide
  have hdescent : baseEnd_51193 < baseStart_51193 := by decide
  rcases family_descends (prefixWord ++ tailWord_51193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51336 : List Nat := [2, 1, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_51336 : Nat := 118140960795 + 51336 * 2 ^ 59
def prefixEnd_51336 : Nat := 4983230072969 + 3 ^ 40 * 51336 * 2
def baseEnd_51336 : Nat := 17573361919544254242611

theorem tailTrace_51336 : CollatzResearch.WordTrace tailWord_51336 prefixEnd_51336 17573361919544254242611 := by
  unfold tailWord_51336
  simp only [CollatzResearch.WordTrace]
  refine ⟨936188871012957167946931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1248251828017276223929241 936188871012957167946931)
  ·
    refine ⟨1404283306519435751920397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936188871012957167946931 1404283306519435751920397)
    ·
      refine ⟨526606239944788406970149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1404283306519435751920397 526606239944788406970149)
      ·
        refine ⟨98738669989647826306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526606239944788406970149 98738669989647826306903)
        ·
          refine ⟨148108004984471739460355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98738669989647826306903 148108004984471739460355)
          ·
            refine ⟨222162007476707609190533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148108004984471739460355 222162007476707609190533)
            ·
              refine ⟨41655376401882676723225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222162007476707609190533 41655376401882676723225)
              ·
                refine ⟨31241532301412007542419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41655376401882676723225 31241532301412007542419)
                ·
                  refine ⟨46862298452118011313629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31241532301412007542419 46862298452118011313629)
                  ·
                    refine ⟨17573361919544254242611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46862298452118011313629 17573361919544254242611)
                    ·
                      rfl

theorem cell22_51336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_51336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51336 prefixEnd_51336 := by exact prefixLift 51336
  have htrace : WordTrace (prefixWord ++ tailWord_51336) baseStart_51336 baseEnd_51336 := by
    simpa [prefixWord, tailWord_51336, baseEnd_51336] using wordTrace_append hprefix tailTrace_51336
  have hstable : (prefixWord ++ tailWord_51336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51336).length < 2 ^ (prefixWord ++ tailWord_51336).sum := by decide
  have hdescent : baseEnd_51336 < baseStart_51336 := by decide
  rcases family_descends (prefixWord ++ tailWord_51336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51360 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 6]
def baseStart_51360 : Nat := 118140960795 + 51360 * 2 ^ 59
def prefixEnd_51360 : Nat := 4983230072969 + 3 ^ 40 * 51360 * 2
def baseEnd_51360 : Nat := 5860525870005397214179

theorem tailTrace_51360 : CollatzResearch.WordTrace tailWord_51360 prefixEnd_51360 5860525870005397214179 := by
  unfold tailWord_51360
  simp only [CollatzResearch.WordTrace]
  refine ⟨936626546969483217383767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1248835395959310956511689 936626546969483217383767)
  ·
    refine ⟨1404939820454224826075651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936626546969483217383767 1404939820454224826075651)
    ·
      refine ⟨2107409730681337239113477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404939820454224826075651 2107409730681337239113477)
      ·
        refine ⟨395139324502750732333777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2107409730681337239113477 395139324502750732333777)
        ·
          refine ⟨296354493377063049250333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395139324502750732333777 296354493377063049250333)
          ·
            refine ⟨111132935016398643468875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296354493377063049250333 111132935016398643468875)
            ·
              refine ⟨166699402524597965203313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111132935016398643468875 166699402524597965203313)
              ·
                refine ⟨125024551893448473902485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166699402524597965203313 125024551893448473902485)
                ·
                  refine ⟨5860525870005397214179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125024551893448473902485 5860525870005397214179)
                  ·
                    rfl

theorem cell22_51360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_51360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51360 prefixEnd_51360 := by exact prefixLift 51360
  have htrace : WordTrace (prefixWord ++ tailWord_51360) baseStart_51360 baseEnd_51360 := by
    simpa [prefixWord, tailWord_51360, baseEnd_51360] using wordTrace_append hprefix tailTrace_51360
  have hstable : (prefixWord ++ tailWord_51360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51360).length < 2 ^ (prefixWord ++ tailWord_51360).sum := by decide
  have hdescent : baseEnd_51360 < baseStart_51360 := by decide
  rcases family_descends (prefixWord ++ tailWord_51360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51362 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_51362 : Nat := 118140960795 + 51362 * 2 ^ 59
def prefixEnd_51362 : Nat := 4983230072969 + 3 ^ 40 * 51362 * 2
def baseEnd_51362 : Nat := 17582262250888853092531

theorem tailTrace_51362 : CollatzResearch.WordTrace tailWord_51362 prefixEnd_51362 17582262250888853092531 := by
  unfold tailWord_51362
  simp only [CollatzResearch.WordTrace]
  refine ⟨468331509982930194085085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1248884026621147184226893 468331509982930194085085)
  ·
    refine ⟨175624316243598822781907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 468331509982930194085085 175624316243598822781907)
    ·
      refine ⟨263436474365398234172861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175624316243598822781907 263436474365398234172861)
      ·
        refine ⟨98788677887024337814823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263436474365398234172861 98788677887024337814823)
        ·
          refine ⟨148183016830536506722235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98788677887024337814823 148183016830536506722235)
          ·
            refine ⟨222274525245804760083353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148183016830536506722235 222274525245804760083353)
            ·
              refine ⟨166705893934353570062515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222274525245804760083353 166705893934353570062515)
              ·
                refine ⟨250058840901530355093773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166705893934353570062515 250058840901530355093773)
                ·
                  refine ⟨93772065338073883160165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250058840901530355093773 93772065338073883160165)
                  ·
                    refine ⟨17582262250888853092531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93772065338073883160165 17582262250888853092531)
                    ·
                      rfl

theorem cell22_51362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_51362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51362 prefixEnd_51362 := by exact prefixLift 51362
  have htrace : WordTrace (prefixWord ++ tailWord_51362) baseStart_51362 baseEnd_51362 := by
    simpa [prefixWord, tailWord_51362, baseEnd_51362] using wordTrace_append hprefix tailTrace_51362
  have hstable : (prefixWord ++ tailWord_51362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51362).length < 2 ^ (prefixWord ++ tailWord_51362).sum := by decide
  have hdescent : baseEnd_51362 < baseStart_51362 := by decide
  rcases family_descends (prefixWord ++ tailWord_51362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51375 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 4, 3]
def baseStart_51375 : Nat := 118140960795 + 51375 * 2 ^ 59
def prefixEnd_51375 : Nat := 4983230072969 + 3 ^ 40 * 51375 * 2
def baseEnd_51375 : Nat := 17586712416561152517491

theorem tailTrace_51375 : CollatzResearch.WordTrace tailWord_51375 prefixEnd_51375 17586712416561152517491 := by
  unfold tailWord_51375
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873800188884623996563579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1249200125923082664375719 1873800188884623996563579)
  ·
    refine ⟨2810700283326935994845369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873800188884623996563579 2810700283326935994845369)
    ·
      refine ⟨2108025212495201996134027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2810700283326935994845369 2108025212495201996134027)
      ·
        refine ⟨3162037818742802994201041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108025212495201996134027 3162037818742802994201041)
        ·
          refine ⟨2371528364057102245650781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162037818742802994201041 2371528364057102245650781)
          ·
            refine ⟨889323136521413342119043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2371528364057102245650781 889323136521413342119043)
            ·
              refine ⟨1333984704782120013178565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889323136521413342119043 1333984704782120013178565)
              ·
                refine ⟨250122132146647502470981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1333984704782120013178565 250122132146647502470981)
                ·
                  refine ⟨46897899777496406713309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250122132146647502470981 46897899777496406713309)
                  ·
                    refine ⟨17586712416561152517491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46897899777496406713309 17586712416561152517491)
                    ·
                      rfl

theorem cell22_51375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_51375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51375 prefixEnd_51375 := by exact prefixLift 51375
  have htrace : WordTrace (prefixWord ++ tailWord_51375) baseStart_51375 baseEnd_51375 := by
    simpa [prefixWord, tailWord_51375, baseEnd_51375] using wordTrace_append hprefix tailTrace_51375
  have hstable : (prefixWord ++ tailWord_51375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51375).length < 2 ^ (prefixWord ++ tailWord_51375).sum := by decide
  have hdescent : baseEnd_51375 < baseStart_51375 := by decide
  rcases family_descends (prefixWord ++ tailWord_51375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51392 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_51392 : Nat := 118140960795 + 51392 * 2 ^ 59
def prefixEnd_51392 : Nat := 4983230072969 + 3 ^ 40 * 51392 * 2
def baseEnd_51392 : Nat := 17592531863978774842439

theorem tailTrace_51392 : CollatzResearch.WordTrace tailWord_51392 prefixEnd_51392 17592531863978774842439 := by
  unfold tailWord_51392
  simp only [CollatzResearch.WordTrace]
  refine ⟨937210114911517949966215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1249613486548690599954953 937210114911517949966215)
  ·
    refine ⟨1405815172367276924949323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937210114911517949966215 1405815172367276924949323)
    ·
      refine ⟨2108722758550915387423985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405815172367276924949323 2108722758550915387423985)
      ·
        refine ⟨1581542068913186540567989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108722758550915387423985 1581542068913186540567989)
        ·
          refine ⟨148269568960611238178249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1581542068913186540567989 148269568960611238178249)
          ·
            refine ⟨111202176720458428633687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148269568960611238178249 111202176720458428633687)
            ·
              refine ⟨166803265080687642950531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111202176720458428633687 166803265080687642950531)
              ·
                refine ⟨250204897621031464425797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166803265080687642950531 250204897621031464425797)
                ·
                  refine ⟨46913418303943399579837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250204897621031464425797 46913418303943399579837)
                  ·
                    refine ⟨17592531863978774842439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46913418303943399579837 17592531863978774842439)
                    ·
                      rfl

theorem cell22_51392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_51392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51392 prefixEnd_51392 := by exact prefixLift 51392
  have htrace : WordTrace (prefixWord ++ tailWord_51392) baseStart_51392 baseEnd_51392 := by
    simpa [prefixWord, tailWord_51392, baseEnd_51392] using wordTrace_append hprefix tailTrace_51392
  have hstable : (prefixWord ++ tailWord_51392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51392).length < 2 ^ (prefixWord ++ tailWord_51392).sum := by decide
  have hdescent : baseEnd_51392 < baseStart_51392 := by decide
  rcases family_descends (prefixWord ++ tailWord_51392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51394 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_51394 : Nat := 118140960795 + 51394 * 2 ^ 59
def prefixEnd_51394 : Nat := 4983230072969 + 3 ^ 40 * 51394 * 2
def baseEnd_51394 : Nat := 5864405501617145430811

theorem tailTrace_51394 : CollatzResearch.WordTrace tailWord_51394 prefixEnd_51394 5864405501617145430811 := by
  unfold tailWord_51394
  simp only [CollatzResearch.WordTrace]
  refine ⟨468623293953947560376309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1249662117210526827670157 468623293953947560376309)
  ·
    refine ⟨43933433808182583785279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 468623293953947560376309 43933433808182583785279)
    ·
      refine ⟨65900150712273875677919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43933433808182583785279 65900150712273875677919)
      ·
        refine ⟨98850226068410813516879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65900150712273875677919 98850226068410813516879)
        ·
          refine ⟨148275339102616220275319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98850226068410813516879 148275339102616220275319)
          ·
            refine ⟨222413008653924330412979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148275339102616220275319 222413008653924330412979)
            ·
              refine ⟨333619512980886495619469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222413008653924330412979 333619512980886495619469)
              ·
                refine ⟨125107317367832435857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333619512980886495619469 125107317367832435857301)
                ·
                  refine ⟨5864405501617145430811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125107317367832435857301 5864405501617145430811)
                  ·
                    rfl

theorem cell22_51394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_51394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51394 prefixEnd_51394 := by exact prefixLift 51394
  have htrace : WordTrace (prefixWord ++ tailWord_51394) baseStart_51394 baseEnd_51394 := by
    simpa [prefixWord, tailWord_51394, baseEnd_51394] using wordTrace_append hprefix tailTrace_51394
  have hstable : (prefixWord ++ tailWord_51394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51394).length < 2 ^ (prefixWord ++ tailWord_51394).sum := by decide
  have hdescent : baseEnd_51394 < baseStart_51394 := by decide
  rcases family_descends (prefixWord ++ tailWord_51394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51450 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_51450 : Nat := 118140960795 + 51450 * 2 ^ 59
def prefixEnd_51450 : Nat := 4983230072969 + 3 ^ 40 * 51450 * 2
def baseEnd_51450 : Nat := 5870795483095318964087

theorem tailTrace_51450 : CollatzResearch.WordTrace tailWord_51450 prefixEnd_51450 5870795483095318964087 := by
  unfold tailWord_51450
  simp only [CollatzResearch.WordTrace]
  refine ⟨469133915903227951385951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1251023775741941203695869 469133915903227951385951)
  ·
    refine ⟨703700873854841927078927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469133915903227951385951 703700873854841927078927)
    ·
      refine ⟨1055551310782262890618391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703700873854841927078927 1055551310782262890618391)
      ·
        refine ⟨1583326966173394335927587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055551310782262890618391 1583326966173394335927587)
        ·
          refine ⟨2374990449260091503891381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583326966173394335927587 2374990449260091503891381)
          ·
            refine ⟨222655354618133578489817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2374990449260091503891381 222655354618133578489817)
            ·
              refine ⟨166991515963600183867363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222655354618133578489817 166991515963600183867363)
              ·
                refine ⟨250487273945400275801045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166991515963600183867363 250487273945400275801045)
                ·
                  refine ⟨5870795483095318964087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250487273945400275801045 5870795483095318964087)
                  ·
                    rfl

theorem cell22_51450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_51450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51450 prefixEnd_51450 := by exact prefixLift 51450
  have htrace : WordTrace (prefixWord ++ tailWord_51450) baseStart_51450 baseEnd_51450 := by
    simpa [prefixWord, tailWord_51450, baseEnd_51450] using wordTrace_append hprefix tailTrace_51450
  have hstable : (prefixWord ++ tailWord_51450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51450).length < 2 ^ (prefixWord ++ tailWord_51450).sum := by decide
  have hdescent : baseEnd_51450 < baseStart_51450 := by decide
  rcases family_descends (prefixWord ++ tailWord_51450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51501 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 5]
def baseStart_51501 : Nat := 118140960795 + 51501 * 2 ^ 59
def prefixEnd_51501 : Nat := 4983230072969 + 3 ^ 40 * 51501 * 2
def baseEnd_51501 : Nat := 5876614930512941289035

theorem tailTrace_51501 : CollatzResearch.WordTrace tailWord_51501 prefixEnd_51501 5876614930512941289035 := by
  unfold tailWord_51501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878395786428147515650357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1252263857618765010433571 1878395786428147515650357)
  ·
    refine ⟨176099604977638829592221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1878395786428147515650357 176099604977638829592221)
    ·
      refine ⟨66037351866614561097083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176099604977638829592221 66037351866614561097083)
      ·
        refine ⟨99056027799921841645625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66037351866614561097083 99056027799921841645625)
        ·
          refine ⟨74292020849941381234219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99056027799921841645625 74292020849941381234219)
          ·
            refine ⟨111438031274912071851329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74292020849941381234219 111438031274912071851329)
            ·
              refine ⟨83578523456184053888497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111438031274912071851329 83578523456184053888497)
              ·
                refine ⟨62683892592138040416373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83578523456184053888497 62683892592138040416373)
                ·
                  refine ⟨5876614930512941289035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62683892592138040416373 5876614930512941289035)
                  ·
                    rfl

theorem cell22_51501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_51501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51501 prefixEnd_51501 := by exact prefixLift 51501
  have htrace : WordTrace (prefixWord ++ tailWord_51501) baseStart_51501 baseEnd_51501 := by
    simpa [prefixWord, tailWord_51501, baseEnd_51501] using wordTrace_append hprefix tailTrace_51501
  have hstable : (prefixWord ++ tailWord_51501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51501).length < 2 ^ (prefixWord ++ tailWord_51501).sum := by decide
  have hdescent : baseEnd_51501 < baseStart_51501 := by decide
  rcases family_descends (prefixWord ++ tailWord_51501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51505 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_51505 : Nat := 118140960795 + 51505 * 2 ^ 59
def prefixEnd_51505 : Nat := 4983230072969 + 3 ^ 40 * 51505 * 2
def baseEnd_51505 : Nat := 17631214073284146767093

theorem tailTrace_51505 : CollatzResearch.WordTrace tailWord_51505 prefixEnd_51505 17631214073284146767093 := by
  unfold tailWord_51505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878541678413656198795969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1252361118942437465863979 1878541678413656198795969)
  ·
    refine ⟨1408906258810242149096977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1878541678413656198795969 1408906258810242149096977)
    ·
      refine ⟨1056679694107681611822733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1408906258810242149096977 1056679694107681611822733)
      ·
        refine ⟨396254885290380604433525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1056679694107681611822733 396254885290380604433525)
        ·
          refine ⟨37148895495973181665643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 396254885290380604433525 37148895495973181665643)
          ·
            refine ⟨55723343243959772498465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37148895495973181665643 55723343243959772498465)
            ·
              refine ⟨41792507432969829373849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55723343243959772498465 41792507432969829373849)
              ·
                refine ⟨31344380574727372030387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41792507432969829373849 31344380574727372030387)
                ·
                  refine ⟨47016570862091058045581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31344380574727372030387 47016570862091058045581)
                  ·
                    refine ⟨17631214073284146767093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47016570862091058045581 17631214073284146767093)
                    ·
                      rfl

theorem cell22_51505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_51505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51505 prefixEnd_51505 := by exact prefixLift 51505
  have htrace : WordTrace (prefixWord ++ tailWord_51505) baseStart_51505 baseEnd_51505 := by
    simpa [prefixWord, tailWord_51505, baseEnd_51505] using wordTrace_append hprefix tailTrace_51505
  have hstable : (prefixWord ++ tailWord_51505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51505).length < 2 ^ (prefixWord ++ tailWord_51505).sum := by decide
  have hdescent : baseEnd_51505 < baseStart_51505 := by decide
  rcases family_descends (prefixWord ++ tailWord_51505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51527 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 5]
def baseStart_51527 : Nat := 118140960795 + 51527 * 2 ^ 59
def prefixEnd_51527 : Nat := 4983230072969 + 3 ^ 40 * 51527 * 2
def baseEnd_51527 : Nat := 17638745122883422717025

theorem tailTrace_51527 : CollatzResearch.WordTrace tailWord_51527 prefixEnd_51527 17638745122883422717025 := by
  unfold tailWord_51527
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879344084333953956096835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1252896056222635970731223 1879344084333953956096835)
  ·
    refine ⟨2819016126500930934145253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879344084333953956096835 2819016126500930934145253)
    ·
      refine ⟨528565523718924550152235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2819016126500930934145253 528565523718924550152235)
      ·
        refine ⟨792848285578386825228353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528565523718924550152235 792848285578386825228353)
        ·
          refine ⟨594636214183790118921265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792848285578386825228353 594636214183790118921265)
          ·
            refine ⟨445977160637842589190949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594636214183790118921265 445977160637842589190949)
            ·
              refine ⟨83620717619595485473303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 445977160637842589190949 83620717619595485473303)
              ·
                refine ⟨125431076429393228209955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83620717619595485473303 125431076429393228209955)
                ·
                  refine ⟨188146614644089842314933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125431076429393228209955 188146614644089842314933)
                  ·
                    refine ⟨17638745122883422717025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 188146614644089842314933 17638745122883422717025)
                    ·
                      rfl

theorem cell22_51527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_51527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51527 prefixEnd_51527 := by exact prefixLift 51527
  have htrace : WordTrace (prefixWord ++ tailWord_51527) baseStart_51527 baseEnd_51527 := by
    simpa [prefixWord, tailWord_51527, baseEnd_51527] using wordTrace_append hprefix tailTrace_51527
  have hstable : (prefixWord ++ tailWord_51527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51527).length < 2 ^ (prefixWord ++ tailWord_51527).sum := by decide
  have hdescent : baseEnd_51527 < baseStart_51527 := by decide
  rcases family_descends (prefixWord ++ tailWord_51527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51709 : List Nat := [1, 4, 1, 1, 1, 3, 5, 6]
def baseStart_51709 : Nat := 118140960795 + 51709 * 2 ^ 59
def prefixEnd_51709 : Nat := 4983230072969 + 3 ^ 40 * 51709 * 2
def baseEnd_51709 : Nat := 1966783049143957185163

theorem tailTrace_51709 : CollatzResearch.WordTrace tailWord_51709 prefixEnd_51709 1966783049143957185163 := by
  unfold tailWord_51709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885982169674599039222181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257321446449732692814787 1885982169674599039222181)
  ·
    refine ⟨353621656813987319854159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1885982169674599039222181 353621656813987319854159)
    ·
      refine ⟨530432485220980979781239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353621656813987319854159 530432485220980979781239)
      ·
        refine ⟨795648727831471469671859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530432485220980979781239 795648727831471469671859)
        ·
          refine ⟨1193473091747207204507789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795648727831471469671859 1193473091747207204507789)
          ·
            refine ⟨447552409405202701690421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1193473091747207204507789 447552409405202701690421)
            ·
              refine ⟨41958038381737753283477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447552409405202701690421 41958038381737753283477)
              ·
                refine ⟨1966783049143957185163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41958038381737753283477 1966783049143957185163)
                ·
                  rfl

theorem cell22_51709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 6].length) (baseStart_51709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51709 prefixEnd_51709 := by exact prefixLift 51709
  have htrace : WordTrace (prefixWord ++ tailWord_51709) baseStart_51709 baseEnd_51709 := by
    simpa [prefixWord, tailWord_51709, baseEnd_51709] using wordTrace_append hprefix tailTrace_51709
  have hstable : (prefixWord ++ tailWord_51709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51709).length < 2 ^ (prefixWord ++ tailWord_51709).sum := by decide
  have hdescent : baseEnd_51709 < baseStart_51709 := by decide
  rcases family_descends (prefixWord ++ tailWord_51709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51737 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 7]
def baseStart_51737 : Nat := 118140960795 + 51737 * 2 ^ 59
def prefixEnd_51737 : Nat := 4983230072969 + 3 ^ 40 * 51737 * 2
def baseEnd_51737 : Nat := 5903544138170958322127

theorem tailTrace_51737 : CollatzResearch.WordTrace tailWord_51737 prefixEnd_51737 5903544138170958322127 := by
  unfold tailWord_51737
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887003413573159821241465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258002275715439880827643 1887003413573159821241465)
  ·
    refine ⟨1415252560179869865931099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1887003413573159821241465 1415252560179869865931099)
    ·
      refine ⟨2122878840269804798896649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415252560179869865931099 2122878840269804798896649)
      ·
        refine ⟨1592159130202353599172487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2122878840269804798896649 1592159130202353599172487)
        ·
          refine ⟨2388238695303530398758731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592159130202353599172487 2388238695303530398758731)
          ·
            refine ⟨3582358042955295598138097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388238695303530398758731 3582358042955295598138097)
            ·
              refine ⟨2686768532216471698603573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582358042955295598138097 2686768532216471698603573)
              ·
                refine ⟨251884549895294221744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2686768532216471698603573 251884549895294221744085)
                ·
                  refine ⟨5903544138170958322127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251884549895294221744085 5903544138170958322127)
                  ·
                    rfl

theorem cell22_51737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_51737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51737 prefixEnd_51737 := by exact prefixLift 51737
  have htrace : WordTrace (prefixWord ++ tailWord_51737) baseStart_51737 baseEnd_51737 := by
    simpa [prefixWord, tailWord_51737, baseEnd_51737] using wordTrace_append hprefix tailTrace_51737
  have hstable : (prefixWord ++ tailWord_51737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51737).length < 2 ^ (prefixWord ++ tailWord_51737).sum := by decide
  have hdescent : baseEnd_51737 < baseStart_51737 := by decide
  rcases family_descends (prefixWord ++ tailWord_51737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51741 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_51741 : Nat := 118140960795 + 51741 * 2 ^ 59
def prefixEnd_51741 : Nat := 4983230072969 + 3 ^ 40 * 51741 * 2
def baseEnd_51741 : Nat := 17712001696258197866369

theorem tailTrace_51741 : CollatzResearch.WordTrace tailWord_51741 prefixEnd_51741 17712001696258197866369 := by
  unfold tailWord_51741
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887149305558668504387077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258099537039112336258051 1887149305558668504387077)
  ·
    refine ⟨353840494792250344572577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1887149305558668504387077 353840494792250344572577)
    ·
      refine ⟨265380371094187758429433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353840494792250344572577 265380371094187758429433)
      ·
        refine ⟨199035278320640818822075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265380371094187758429433 199035278320640818822075)
        ·
          refine ⟨298552917480961228233113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199035278320640818822075 298552917480961228233113)
          ·
            refine ⟨223914688110720921174835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298552917480961228233113 223914688110720921174835)
            ·
              refine ⟨335872032166081381762253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223914688110720921174835 335872032166081381762253)
              ·
                refine ⟨125952012062280518160845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335872032166081381762253 125952012062280518160845)
                ·
                  refine ⟨47232004523355194310317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125952012062280518160845 47232004523355194310317)
                  ·
                    refine ⟨17712001696258197866369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47232004523355194310317 17712001696258197866369)
                    ·
                      rfl

theorem cell22_51741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_51741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51741 prefixEnd_51741 := by exact prefixLift 51741
  have htrace : WordTrace (prefixWord ++ tailWord_51741) baseStart_51741 baseEnd_51741 := by
    simpa [prefixWord, tailWord_51741, baseEnd_51741] using wordTrace_append hprefix tailTrace_51741
  have hstable : (prefixWord ++ tailWord_51741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51741).length < 2 ^ (prefixWord ++ tailWord_51741).sum := by decide
  have hdescent : baseEnd_51741 < baseStart_51741 := by decide
  rcases family_descends (prefixWord ++ tailWord_51741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51844 : List Nat := [2, 3, 2, 1, 3, 11]
def baseStart_51844 : Nat := 118140960795 + 51844 * 2 ^ 59
def prefixEnd_51844 : Nat := 4983230072969 + 3 ^ 40 * 51844 * 2
def baseEnd_51844 : Nat := 219101983965435340013

theorem tailTrace_51844 : CollatzResearch.WordTrace tailWord_51844 prefixEnd_51844 219101983965435340013 := by
  unfold tailWord_51844
  simp only [CollatzResearch.WordTrace]
  refine ⟨945453012092758547693293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1260604016123678063591057 945453012092758547693293)
  ·
    refine ⟨354544879534784455384985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 945453012092758547693293 354544879534784455384985)
    ·
      refine ⟨265908659651088341538739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354544879534784455384985 265908659651088341538739)
      ·
        refine ⟨398862989476632512308109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265908659651088341538739 398862989476632512308109)
        ·
          refine ⟨149573621053737192115541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398862989476632512308109 149573621053737192115541)
          ·
            refine ⟨219101983965435340013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 149573621053737192115541 219101983965435340013)
            ·
              rfl

theorem cell22_51844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 11].length) (baseStart_51844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51844 prefixEnd_51844 := by exact prefixLift 51844
  have htrace : WordTrace (prefixWord ++ tailWord_51844) baseStart_51844 baseEnd_51844 := by
    simpa [prefixWord, tailWord_51844, baseEnd_51844] using wordTrace_append hprefix tailTrace_51844
  have hstable : (prefixWord ++ tailWord_51844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51844).length < 2 ^ (prefixWord ++ tailWord_51844).sum := by decide
  have hdescent : baseEnd_51844 < baseStart_51844 := by decide
  rcases family_descends (prefixWord ++ tailWord_51844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51944 : List Nat := [2, 1, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_51944 : Nat := 118140960795 + 51944 * 2 ^ 59
def prefixEnd_51944 : Nat := 4983230072969 + 3 ^ 40 * 51944 * 2
def baseEnd_51944 : Nat := 17781492744833335040747

theorem tailTrace_51944 : CollatzResearch.WordTrace tailWord_51944 prefixEnd_51944 17781492744833335040747 := by
  unfold tailWord_51944
  simp only [CollatzResearch.WordTrace]
  refine ⟨947276661911617087013443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1263035549215489449351257 947276661911617087013443)
  ·
    refine ⟨1420914992867425630520165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947276661911617087013443 1420914992867425630520165)
    ·
      refine ⟨266421561162642305722531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1420914992867425630520165 266421561162642305722531)
      ·
        refine ⟨399632341743963458583797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266421561162642305722531 399632341743963458583797)
        ·
          refine ⟨37465532038496574242231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 399632341743963458583797 37465532038496574242231)
          ·
            refine ⟨56198298057744861363347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37465532038496574242231 56198298057744861363347)
            ·
              refine ⟨84297447086617292045021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56198298057744861363347 84297447086617292045021)
              ·
                refine ⟨31611542657481484516883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84297447086617292045021 31611542657481484516883)
                ·
                  refine ⟨47417313986222226775325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31611542657481484516883 47417313986222226775325)
                  ·
                    refine ⟨17781492744833335040747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47417313986222226775325 17781492744833335040747)
                    ·
                      rfl

theorem cell22_51944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_51944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51944 prefixEnd_51944 := by exact prefixLift 51944
  have htrace : WordTrace (prefixWord ++ tailWord_51944) baseStart_51944 baseEnd_51944 := by
    simpa [prefixWord, tailWord_51944, baseEnd_51944] using wordTrace_append hprefix tailTrace_51944
  have hstable : (prefixWord ++ tailWord_51944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51944).length < 2 ^ (prefixWord ++ tailWord_51944).sum := by decide
  have hdescent : baseEnd_51944 < baseStart_51944 := by decide
  rcases family_descends (prefixWord ++ tailWord_51944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51983 : List Nat := [1, 1, 2, 1, 1, 1, 7, 3, 2, 3]
def baseStart_51983 : Nat := 118140960795 + 51983 * 2 ^ 59
def prefixEnd_51983 : Nat := 4983230072969 + 3 ^ 40 * 51983 * 2
def baseEnd_51983 : Nat := 17794843241850233315627

theorem tailTrace_51983 : CollatzResearch.WordTrace tailWord_51983 prefixEnd_51983 17794843241850233315627 := by
  unfold tailWord_51983
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895975770681943834696603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1263983847121295889797735 1895975770681943834696603)
  ·
    refine ⟨2843963656022915752044905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895975770681943834696603 2843963656022915752044905)
    ·
      refine ⟨2132972742017186814033679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2843963656022915752044905 2132972742017186814033679)
      ·
        refine ⟨3199459113025780221050519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132972742017186814033679 3199459113025780221050519)
        ·
          refine ⟨4799188669538670331575779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199459113025780221050519 4799188669538670331575779)
          ·
            refine ⟨7198783004308005497363669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799188669538670331575779 7198783004308005497363669)
            ·
              refine ⟨168721476663468878844461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7198783004308005497363669 168721476663468878844461)
              ·
                refine ⟨63270553748800829566673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168721476663468878844461 63270553748800829566673)
                ·
                  refine ⟨47452915311600622175005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63270553748800829566673 47452915311600622175005)
                  ·
                    refine ⟨17794843241850233315627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47452915311600622175005 17794843241850233315627)
                    ·
                      rfl

theorem cell22_51983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_51983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51983 prefixEnd_51983 := by exact prefixLift 51983
  have htrace : WordTrace (prefixWord ++ tailWord_51983) baseStart_51983 baseEnd_51983 := by
    simpa [prefixWord, tailWord_51983, baseEnd_51983] using wordTrace_append hprefix tailTrace_51983
  have hstable : (prefixWord ++ tailWord_51983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51983).length < 2 ^ (prefixWord ++ tailWord_51983).sum := by decide
  have hdescent : baseEnd_51983 < baseStart_51983 := by decide
  rcases family_descends (prefixWord ++ tailWord_51983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51996 : List Nat := [2, 2, 3, 1, 1, 3, 2, 8]
def baseStart_51996 : Nat := 118140960795 + 51996 * 2 ^ 59
def prefixEnd_51996 : Nat := 4983230072969 + 3 ^ 40 * 51996 * 2
def baseEnd_51996 : Nat := 1977699267502503637843

theorem tailTrace_51996 : CollatzResearch.WordTrace tailWord_51996 prefixEnd_51996 1977699267502503637843 := by
  unfold tailWord_51996
  simp only [CollatzResearch.WordTrace]
  refine ⟨948224959817423527459921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1264299946423231369946561 948224959817423527459921)
  ·
    refine ⟨711168719863067645594941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 948224959817423527459921 711168719863067645594941)
    ·
      refine ⟨266688269948650367098103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 711168719863067645594941 266688269948650367098103)
      ·
        refine ⟨400032404922975550647155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266688269948650367098103 400032404922975550647155)
        ·
          refine ⟨600048607384463325970733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400032404922975550647155 600048607384463325970733)
          ·
            refine ⟨225018227769173747239025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600048607384463325970733 225018227769173747239025)
            ·
              refine ⟨168763670826880310429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225018227769173747239025 168763670826880310429269)
              ·
                refine ⟨1977699267502503637843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168763670826880310429269 1977699267502503637843)
                ·
                  rfl

theorem cell22_51996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_51996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_51996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_51996 prefixEnd_51996 := by exact prefixLift 51996
  have htrace : WordTrace (prefixWord ++ tailWord_51996) baseStart_51996 baseEnd_51996 := by
    simpa [prefixWord, tailWord_51996, baseEnd_51996] using wordTrace_append hprefix tailTrace_51996
  have hstable : (prefixWord ++ tailWord_51996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51996).length < 2 ^ (prefixWord ++ tailWord_51996).sum := by decide
  have hdescent : baseEnd_51996 < baseStart_51996 := by decide
  rcases family_descends (prefixWord ++ tailWord_51996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52013 : List Nat := [1, 5, 3, 2, 11]
def baseStart_52013 : Nat := 118140960795 + 52013 * 2 ^ 59
def prefixEnd_52013 : Nat := 4983230072969 + 3 ^ 40 * 52013 * 2
def baseEnd_52013 : Nat := 73272069361893642245

theorem tailTrace_52013 : CollatzResearch.WordTrace tailWord_52013 prefixEnd_52013 73272069361893642245 := by
  unfold tailWord_52013
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897069960573258958288693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1264713307048839305525795 1897069960573258958288693)
  ·
    refine ⟨177850308803743027339565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1897069960573258958288693 177850308803743027339565)
    ·
      refine ⟨66693865801403635252337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177850308803743027339565 66693865801403635252337)
      ·
        refine ⟨50020399351052726439253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66693865801403635252337 50020399351052726439253)
        ·
          refine ⟨73272069361893642245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 50020399351052726439253 73272069361893642245)
          ·
            rfl

theorem cell22_52013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 11].length) (baseStart_52013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52013 prefixEnd_52013 := by exact prefixLift 52013
  have htrace : WordTrace (prefixWord ++ tailWord_52013) baseStart_52013 baseEnd_52013 := by
    simpa [prefixWord, tailWord_52013, baseEnd_52013] using wordTrace_append hprefix tailTrace_52013
  have hstable : (prefixWord ++ tailWord_52013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52013).length < 2 ^ (prefixWord ++ tailWord_52013).sum := by decide
  have hdescent : baseEnd_52013 < baseStart_52013 := by decide
  rcases family_descends (prefixWord ++ tailWord_52013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52028 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_52028 : Nat := 118140960795 + 52028 * 2 ^ 59
def prefixEnd_52028 : Nat := 4983230072969 + 3 ^ 40 * 52028 * 2
def baseEnd_52028 : Nat := 17810247661485115940489

theorem tailTrace_52028 : CollatzResearch.WordTrace tailWord_52028 prefixEnd_52028 17810247661485115940489 := by
  unfold tailWord_52028
  simp only [CollatzResearch.WordTrace]
  refine ⟨948808527759458260042369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1265078037012611013389825 948808527759458260042369)
  ·
    refine ⟨711606395819593695031777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 948808527759458260042369 711606395819593695031777)
    ·
      refine ⟨533704796864695271273833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 711606395819593695031777 533704796864695271273833)
      ·
        refine ⟨400278597648521453455375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533704796864695271273833 400278597648521453455375)
        ·
          refine ⟨600417896472782180183063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400278597648521453455375 600417896472782180183063)
          ·
            refine ⟨900626844709173270274595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600417896472782180183063 900626844709173270274595)
            ·
              refine ⟨1350940267063759905411893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900626844709173270274595 1350940267063759905411893)
              ·
                refine ⟨126650650037227491132365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1350940267063759905411893 126650650037227491132365)
                ·
                  refine ⟨47493993763960309174637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126650650037227491132365 47493993763960309174637)
                  ·
                    refine ⟨17810247661485115940489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47493993763960309174637 17810247661485115940489)
                    ·
                      rfl

theorem cell22_52028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_52028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52028 prefixEnd_52028 := by exact prefixLift 52028
  have htrace : WordTrace (prefixWord ++ tailWord_52028) baseStart_52028 baseEnd_52028 := by
    simpa [prefixWord, tailWord_52028, baseEnd_52028] using wordTrace_append hprefix tailTrace_52028
  have hstable : (prefixWord ++ tailWord_52028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52028).length < 2 ^ (prefixWord ++ tailWord_52028).sum := by decide
  have hdescent : baseEnd_52028 < baseStart_52028 := by decide
  rcases family_descends (prefixWord ++ tailWord_52028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52030 : List Nat := [4, 2, 1, 2, 3, 2, 1, 7]
def baseStart_52030 : Nat := 118140960795 + 52030 * 2 ^ 59
def prefixEnd_52030 : Nat := 4983230072969 + 3 ^ 40 * 52030 * 2
def baseEnd_52030 : Nat := 1978992478039753043387

theorem tailTrace_52030 : CollatzResearch.WordTrace tailWord_52030 prefixEnd_52030 1978992478039753043387 := by
  unfold tailWord_52030
  simp only [CollatzResearch.WordTrace]
  refine ⟨237211250188958857707193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1265126667674447241105029 237211250188958857707193)
  ·
    refine ⟨177908437641719143280395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237211250188958857707193 177908437641719143280395)
    ·
      refine ⟨266862656462578714920593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177908437641719143280395 266862656462578714920593)
      ·
        refine ⟨200146992346934036190445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266862656462578714920593 200146992346934036190445)
        ·
          refine ⟨75055122130100263571417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200146992346934036190445 75055122130100263571417)
          ·
            refine ⟨56291341597575197678563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75055122130100263571417 56291341597575197678563)
            ·
              refine ⟨84437012396362796517845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56291341597575197678563 84437012396362796517845)
              ·
                refine ⟨1978992478039753043387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84437012396362796517845 1978992478039753043387)
                ·
                  rfl

theorem cell22_52030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_52030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52030 prefixEnd_52030 := by exact prefixLift 52030
  have htrace : WordTrace (prefixWord ++ tailWord_52030) baseStart_52030 baseEnd_52030 := by
    simpa [prefixWord, tailWord_52030, baseEnd_52030] using wordTrace_append hprefix tailTrace_52030
  have hstable : (prefixWord ++ tailWord_52030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52030).length < 2 ^ (prefixWord ++ tailWord_52030).sum := by decide
  have hdescent : baseEnd_52030 < baseStart_52030 := by decide
  rcases family_descends (prefixWord ++ tailWord_52030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52103 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 6]
def baseStart_52103 : Nat := 118140960795 + 52103 * 2 ^ 59
def prefixEnd_52103 : Nat := 4983230072969 + 3 ^ 40 * 52103 * 2
def baseEnd_52103 : Nat := 5945307231403306771753

theorem tailTrace_52103 : CollatzResearch.WordTrace tailWord_52103 prefixEnd_52103 5945307231403306771753 := by
  unfold tailWord_52103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900352530247204329064963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1266901686831469552709975 1900352530247204329064963)
  ·
    refine ⟨2850528795370806493597445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900352530247204329064963 2850528795370806493597445)
    ·
      refine ⟨534474149132026217549521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2850528795370806493597445 534474149132026217549521)
      ·
        refine ⟨400855611849019663162141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534474149132026217549521 400855611849019663162141)
        ·
          refine ⟨150320854443382373685803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400855611849019663162141 150320854443382373685803)
          ·
            refine ⟨225481281665073560528705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150320854443382373685803 225481281665073560528705)
            ·
              refine ⟨169110961248805170396529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225481281665073560528705 169110961248805170396529)
              ·
                refine ⟨126833220936603877797397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169110961248805170396529 126833220936603877797397)
                ·
                  refine ⟨5945307231403306771753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126833220936603877797397 5945307231403306771753)
                  ·
                    rfl

theorem cell22_52103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_52103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52103 prefixEnd_52103 := by exact prefixLift 52103
  have htrace : WordTrace (prefixWord ++ tailWord_52103) baseStart_52103 baseEnd_52103 := by
    simpa [prefixWord, tailWord_52103, baseEnd_52103] using wordTrace_append hprefix tailTrace_52103
  have hstable : (prefixWord ++ tailWord_52103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52103).length < 2 ^ (prefixWord ++ tailWord_52103).sum := by decide
  have hdescent : baseEnd_52103 < baseStart_52103 := by decide
  rcases family_descends (prefixWord ++ tailWord_52103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52105 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_52105 : Nat := 118140960795 + 52105 * 2 ^ 59
def prefixEnd_52105 : Nat := 4983230072969 + 3 ^ 40 * 52105 * 2
def baseEnd_52105 : Nat := 17836606335082581765253

theorem tailTrace_52105 : CollatzResearch.WordTrace tailWord_52105 prefixEnd_52105 17836606335082581765253 := by
  unfold tailWord_52105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900425476239958670637769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1266950317493305780425179 1900425476239958670637769)
  ·
    refine ⟨1425319107179969002978327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1900425476239958670637769 1425319107179969002978327)
    ·
      refine ⟨2137978660769953504467491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425319107179969002978327 2137978660769953504467491)
      ·
        refine ⟨3206967991154930256701237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137978660769953504467491 3206967991154930256701237)
        ·
          refine ⟨300653249170774711565741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3206967991154930256701237 300653249170774711565741)
          ·
            refine ⟨112744968439040516837153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300653249170774711565741 112744968439040516837153)
            ·
              refine ⟨84558726329280387627865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112744968439040516837153 84558726329280387627865)
              ·
                refine ⟨63419044746960290720899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84558726329280387627865 63419044746960290720899)
                ·
                  refine ⟨95128567120440436081349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63419044746960290720899 95128567120440436081349)
                  ·
                    refine ⟨17836606335082581765253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95128567120440436081349 17836606335082581765253)
                    ·
                      rfl

theorem cell22_52105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_52105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52105 prefixEnd_52105 := by exact prefixLift 52105
  have htrace : WordTrace (prefixWord ++ tailWord_52105) baseStart_52105 baseEnd_52105 := by
    simpa [prefixWord, tailWord_52105, baseEnd_52105] using wordTrace_append hprefix tailTrace_52105
  have hstable : (prefixWord ++ tailWord_52105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52105).length < 2 ^ (prefixWord ++ tailWord_52105).sum := by decide
  have hdescent : baseEnd_52105 < baseStart_52105 := by decide
  rcases family_descends (prefixWord ++ tailWord_52105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52131 : List Nat := [1, 1, 1, 4, 1, 2, 12]
def baseStart_52131 : Nat := 118140960795 + 52131 * 2 ^ 59
def prefixEnd_52131 : Nat := 4983230072969 + 3 ^ 40 * 52131 * 2
def baseEnd_52131 : Nat := 660944691349154837599

theorem tailTrace_52131 : CollatzResearch.WordTrace tailWord_52131 prefixEnd_52131 660944691349154837599 := by
  unfold tailWord_52131
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901373774145765111084247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1267582516097176740722831 1901373774145765111084247)
  ·
    refine ⟨2852060661218647666626371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901373774145765111084247 2852060661218647666626371)
    ·
      refine ⟨4278090991827971499939557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852060661218647666626371 4278090991827971499939557)
      ·
        refine ⟨802142060967744656238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4278090991827971499939557 802142060967744656238667)
        ·
          refine ⟨1203213091451616984358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802142060967744656238667 1203213091451616984358001)
          ·
            refine ⟨902409818588712738268501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203213091451616984358001 902409818588712738268501)
            ·
              refine ⟨660944691349154837599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 902409818588712738268501 660944691349154837599)
              ·
                rfl

theorem cell22_52131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 12].length) (baseStart_52131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52131 prefixEnd_52131 := by exact prefixLift 52131
  have htrace : WordTrace (prefixWord ++ tailWord_52131) baseStart_52131 baseEnd_52131 := by
    simpa [prefixWord, tailWord_52131, baseEnd_52131] using wordTrace_append hprefix tailTrace_52131
  have hstable : (prefixWord ++ tailWord_52131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52131).length < 2 ^ (prefixWord ++ tailWord_52131).sum := by decide
  have hdescent : baseEnd_52131 < baseStart_52131 := by decide
  rcases family_descends (prefixWord ++ tailWord_52131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52152 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_52152 : Nat := 118140960795 + 52152 * 2 ^ 59
def prefixEnd_52152 : Nat := 4983230072969 + 3 ^ 40 * 52152 * 2
def baseEnd_52152 : Nat := 17852695395590125840109

theorem tailTrace_52152 : CollatzResearch.WordTrace tailWord_52152 prefixEnd_52152 17852695395590125840109 := by
  unfold tailWord_52152
  simp only [CollatzResearch.WordTrace]
  refine ⟨951069853534842848799355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1268093138046457131732473 951069853534842848799355)
  ·
    refine ⟨1426604780302264273199033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951069853534842848799355 1426604780302264273199033)
    ·
      refine ⟨1069953585226698204899275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1426604780302264273199033 1069953585226698204899275)
      ·
        refine ⟨1604930377840047307348913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069953585226698204899275 1604930377840047307348913)
        ·
          refine ⟨1203697783380035480511685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604930377840047307348913 1203697783380035480511685)
          ·
            refine ⟨225693334383756652595941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1203697783380035480511685 225693334383756652595941)
            ·
              refine ⟨42317500196954372361739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225693334383756652595941 42317500196954372361739)
              ·
                refine ⟨63476250295431558542609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42317500196954372361739 63476250295431558542609)
                ·
                  refine ⟨47607187721573668906957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63476250295431558542609 47607187721573668906957)
                  ·
                    refine ⟨17852695395590125840109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47607187721573668906957 17852695395590125840109)
                    ·
                      rfl

theorem cell22_52152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_52152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52152 prefixEnd_52152 := by exact prefixLift 52152
  have htrace : WordTrace (prefixWord ++ tailWord_52152) baseStart_52152 baseEnd_52152 := by
    simpa [prefixWord, tailWord_52152, baseEnd_52152] using wordTrace_append hprefix tailTrace_52152
  have hstable : (prefixWord ++ tailWord_52152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52152).length < 2 ^ (prefixWord ++ tailWord_52152).sum := by decide
  have hdescent : baseEnd_52152 < baseStart_52152 := by decide
  rcases family_descends (prefixWord ++ tailWord_52152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52173 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_52173 : Nat := 118140960795 + 52173 * 2 ^ 59
def prefixEnd_52173 : Nat := 4983230072969 + 3 ^ 40 * 52173 * 2
def baseEnd_52173 : Nat := 17859884124753071065045

theorem tailTrace_52173 : CollatzResearch.WordTrace tailWord_52173 prefixEnd_52173 17859884124753071065045 := by
  unfold tailWord_52173
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902905639993606284113173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1268603759995737522742115 1902905639993606284113173)
  ·
    refine ⟨89198701874700294567805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1902905639993606284113173 89198701874700294567805)
    ·
      refine ⟨33449513203012610462927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89198701874700294567805 33449513203012610462927)
      ·
        refine ⟨50174269804518915694391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33449513203012610462927 50174269804518915694391)
        ·
          refine ⟨75261404706778373541587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50174269804518915694391 75261404706778373541587)
          ·
            refine ⟨112892107060167560312381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75261404706778373541587 112892107060167560312381)
            ·
              refine ⟨42334540147562835117143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112892107060167560312381 42334540147562835117143)
              ·
                refine ⟨63501810221344252675715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42334540147562835117143 63501810221344252675715)
                ·
                  refine ⟨95252715332016379013573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63501810221344252675715 95252715332016379013573)
                  ·
                    refine ⟨17859884124753071065045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95252715332016379013573 17859884124753071065045)
                    ·
                      rfl

theorem cell22_52173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_52173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52173 prefixEnd_52173 := by exact prefixLift 52173
  have htrace : WordTrace (prefixWord ++ tailWord_52173) baseStart_52173 baseEnd_52173 := by
    simpa [prefixWord, tailWord_52173, baseEnd_52173] using wordTrace_append hprefix tailTrace_52173
  have hstable : (prefixWord ++ tailWord_52173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52173).length < 2 ^ (prefixWord ++ tailWord_52173).sum := by decide
  have hdescent : baseEnd_52173 < baseStart_52173 := by decide
  rcases family_descends (prefixWord ++ tailWord_52173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52255 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 6]
def baseStart_52255 : Nat := 118140960795 + 52255 * 2 ^ 59
def prefixEnd_52255 : Nat := 4983230072969 + 3 ^ 40 * 52255 * 2
def baseEnd_52255 : Nat := 5962651466844063504931

theorem tailTrace_52255 : CollatzResearch.WordTrace tailWord_52255 prefixEnd_52255 5962651466844063504931 := by
  unfold tailWord_52255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905896425696534288598219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1270597617131022859065479 1905896425696534288598219)
  ·
    refine ⟨2858844638544801432897329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905896425696534288598219 2858844638544801432897329)
    ·
      refine ⟨2144133478908601074672997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2858844638544801432897329 2144133478908601074672997)
      ·
        refine ⟨402025027295362701501187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2144133478908601074672997 402025027295362701501187)
        ·
          refine ⟨603037540943044052251781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402025027295362701501187 603037540943044052251781)
          ·
            refine ⟨113069538926820759797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 603037540943044052251781 113069538926820759797209)
            ·
              refine ⟨84802154195115569847907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113069538926820759797209 84802154195115569847907)
              ·
                refine ⟨127203231292673354771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84802154195115569847907 127203231292673354771861)
                ·
                  refine ⟨5962651466844063504931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127203231292673354771861 5962651466844063504931)
                  ·
                    rfl

theorem cell22_52255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_52255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52255 prefixEnd_52255 := by exact prefixLift 52255
  have htrace : WordTrace (prefixWord ++ tailWord_52255) baseStart_52255 baseEnd_52255 := by
    simpa [prefixWord, tailWord_52255, baseEnd_52255] using wordTrace_append hprefix tailTrace_52255
  have hstable : (prefixWord ++ tailWord_52255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52255).length < 2 ^ (prefixWord ++ tailWord_52255).sum := by decide
  have hdescent : baseEnd_52255 < baseStart_52255 := by decide
  rcases family_descends (prefixWord ++ tailWord_52255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52268 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_52268 : Nat := 118140960795 + 52268 * 2 ^ 59
def prefixEnd_52268 : Nat := 4983230072969 + 3 ^ 40 * 52268 * 2
def baseEnd_52268 : Nat := 17892404566204489939753

theorem tailTrace_52268 : CollatzResearch.WordTrace tailWord_52268 prefixEnd_52268 17892404566204489939753 := by
  unfold tailWord_52268
  simp only [CollatzResearch.WordTrace]
  refine ⟨953185287324718754410729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1270913716432958339214305 953185287324718754410729)
  ·
    refine ⟨714888965493539065808047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 953185287324718754410729 714888965493539065808047)
    ·
      refine ⟨1072333448240308598712071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714888965493539065808047 1072333448240308598712071)
      ·
        refine ⟨1608500172360462898068107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072333448240308598712071 1608500172360462898068107)
        ·
          refine ⟨2412750258540694347102161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608500172360462898068107 2412750258540694347102161)
          ·
            refine ⟨1809562693905520760326621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2412750258540694347102161 1809562693905520760326621)
            ·
              refine ⟨678586010214570285122483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809562693905520760326621 678586010214570285122483)
              ·
                refine ⟨1017879015321855427683725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678586010214570285122483 1017879015321855427683725)
                ·
                  refine ⟨381704630745695785381397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017879015321855427683725 381704630745695785381397)
                  ·
                    refine ⟨17892404566204489939753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 381704630745695785381397 17892404566204489939753)
                    ·
                      rfl

theorem cell22_52268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_52268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52268 prefixEnd_52268 := by exact prefixLift 52268
  have htrace : WordTrace (prefixWord ++ tailWord_52268) baseStart_52268 baseEnd_52268 := by
    simpa [prefixWord, tailWord_52268, baseEnd_52268] using wordTrace_append hprefix tailTrace_52268
  have hstable : (prefixWord ++ tailWord_52268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52268).length < 2 ^ (prefixWord ++ tailWord_52268).sum := by decide
  have hdescent : baseEnd_52268 < baseStart_52268 := by decide
  rcases family_descends (prefixWord ++ tailWord_52268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52285 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_52285 : Nat := 118140960795 + 52285 * 2 ^ 59
def prefixEnd_52285 : Nat := 4983230072969 + 3 ^ 40 * 52285 * 2
def baseEnd_52285 : Nat := 17898224013622112264701

theorem tailTrace_52285 : CollatzResearch.WordTrace tailWord_52285 prefixEnd_52285 17898224013622112264701 := by
  unfold tailWord_52285
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906990615587849412190309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1271327077058566274793539 1906990615587849412190309)
  ·
    refine ⟨357560740422721764785683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1906990615587849412190309 357560740422721764785683)
    ·
      refine ⟨536341110634082647178525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357560740422721764785683 536341110634082647178525)
      ·
        refine ⟨201127916487780992691947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536341110634082647178525 201127916487780992691947)
        ·
          refine ⟨301691874731671489037921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201127916487780992691947 301691874731671489037921)
          ·
            refine ⟨226268906048753616778441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301691874731671489037921 226268906048753616778441)
            ·
              refine ⟨169701679536565212583831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226268906048753616778441 169701679536565212583831)
              ·
                refine ⟨254552519304847818875747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169701679536565212583831 254552519304847818875747)
                ·
                  refine ⟨381828778957271728313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254552519304847818875747 381828778957271728313621)
                  ·
                    refine ⟨17898224013622112264701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 381828778957271728313621 17898224013622112264701)
                    ·
                      rfl

theorem cell22_52285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_52285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52285 prefixEnd_52285 := by exact prefixLift 52285
  have htrace : WordTrace (prefixWord ++ tailWord_52285) baseStart_52285 baseEnd_52285 := by
    simpa [prefixWord, tailWord_52285, baseEnd_52285] using wordTrace_append hprefix tailTrace_52285
  have hstable : (prefixWord ++ tailWord_52285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52285).length < 2 ^ (prefixWord ++ tailWord_52285).sum := by decide
  have hdescent : baseEnd_52285 < baseStart_52285 := by decide
  rcases family_descends (prefixWord ++ tailWord_52285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52349 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_52349 : Nat := 118140960795 + 52349 * 2 ^ 59
def prefixEnd_52349 : Nat := 4983230072969 + 3 ^ 40 * 52349 * 2
def baseEnd_52349 : Nat := 17920132521547278664505

theorem tailTrace_52349 : CollatzResearch.WordTrace tailWord_52349 prefixEnd_52349 17920132521547278664505 := by
  unfold tailWord_52349
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909324887355988342520101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1272883258237325561680067 1909324887355988342520101)
  ·
    refine ⟨357998416379247814222519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1909324887355988342520101 357998416379247814222519)
    ·
      refine ⟨536997624568871721333779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357998416379247814222519 536997624568871721333779)
      ·
        refine ⟨805496436853307582000669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536997624568871721333779 805496436853307582000669)
        ·
          refine ⟨302061163819990343250251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805496436853307582000669 302061163819990343250251)
          ·
            refine ⟨453091745729985514875377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302061163819990343250251 453091745729985514875377)
            ·
              refine ⟨339818809297489136156533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453091745729985514875377 339818809297489136156533)
              ·
                refine ⟨31858013371639606514675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339818809297489136156533 31858013371639606514675)
                ·
                  refine ⟨47787020057459409772013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31858013371639606514675 47787020057459409772013)
                  ·
                    refine ⟨17920132521547278664505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47787020057459409772013 17920132521547278664505)
                    ·
                      rfl

theorem cell22_52349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_52349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52349 prefixEnd_52349 := by exact prefixLift 52349
  have htrace : WordTrace (prefixWord ++ tailWord_52349) baseStart_52349 baseEnd_52349 := by
    simpa [prefixWord, tailWord_52349, baseEnd_52349] using wordTrace_append hprefix tailTrace_52349
  have hstable : (prefixWord ++ tailWord_52349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52349).length < 2 ^ (prefixWord ++ tailWord_52349).sum := by decide
  have hdescent : baseEnd_52349 < baseStart_52349 := by decide
  rcases family_descends (prefixWord ++ tailWord_52349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52362 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_52362 : Nat := 118140960795 + 52362 * 2 ^ 59
def prefixEnd_52362 : Nat := 4983230072969 + 3 ^ 40 * 52362 * 2
def baseEnd_52362 : Nat := 5974860895739859363155

theorem tailTrace_52362 : CollatzResearch.WordTrace tailWord_52362 prefixEnd_52362 5974860895739859363155 := by
  unfold tailWord_52362
  simp only [CollatzResearch.WordTrace]
  refine ⟨477449759077222890685835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1273199357539261041828893 477449759077222890685835)
  ·
    refine ⟨716174638615834336028753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 477449759077222890685835 716174638615834336028753)
    ·
      refine ⟨537130978961875752021565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 716174638615834336028753 537130978961875752021565)
      ·
        refine ⟨201424117110703407008087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537130978961875752021565 201424117110703407008087)
        ·
          refine ⟨302136175666055110512131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201424117110703407008087 302136175666055110512131)
          ·
            refine ⟨453204263499082665768197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302136175666055110512131 453204263499082665768197)
            ·
              refine ⟨84975799406077999831537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 453204263499082665768197 84975799406077999831537)
              ·
                refine ⟨63731849554558499873653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84975799406077999831537 63731849554558499873653)
                ·
                  refine ⟨5974860895739859363155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63731849554558499873653 5974860895739859363155)
                  ·
                    rfl

theorem cell22_52362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_52362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52362 prefixEnd_52362 := by exact prefixLift 52362
  have htrace : WordTrace (prefixWord ++ tailWord_52362) baseStart_52362 baseEnd_52362 := by
    simpa [prefixWord, tailWord_52362, baseEnd_52362] using wordTrace_append hprefix tailTrace_52362
  have hstable : (prefixWord ++ tailWord_52362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52362).length < 2 ^ (prefixWord ++ tailWord_52362).sum := by decide
  have hdescent : baseEnd_52362 < baseStart_52362 := by decide
  rcases family_descends (prefixWord ++ tailWord_52362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52366 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_52366 : Nat := 118140960795 + 52366 * 2 ^ 59
def prefixEnd_52366 : Nat := 4983230072969 + 3 ^ 40 * 52366 * 2
def baseEnd_52366 : Nat := 17925951968964900989453

theorem tailTrace_52366 : CollatzResearch.WordTrace tailWord_52366 prefixEnd_52366 17925951968964900989453 := by
  unfold tailWord_52366
  simp only [CollatzResearch.WordTrace]
  refine ⟨238743116036800030736119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1273296618862933497259301 238743116036800030736119)
  ·
    refine ⟨358114674055200046104179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238743116036800030736119 358114674055200046104179)
    ·
      refine ⟨537172011082800069156269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358114674055200046104179 537172011082800069156269)
      ·
        refine ⟨201439504156050025933601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 537172011082800069156269 201439504156050025933601)
        ·
          refine ⟨151079628117037519450201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201439504156050025933601 151079628117037519450201)
          ·
            refine ⟨113309721087778139587651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151079628117037519450201 113309721087778139587651)
            ·
              refine ⟨169964581631667209381477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113309721087778139587651 169964581631667209381477)
              ·
                refine ⟨31868359055937601759027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169964581631667209381477 31868359055937601759027)
                ·
                  refine ⟨47802538583906402638541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31868359055937601759027 47802538583906402638541)
                  ·
                    refine ⟨17925951968964900989453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47802538583906402638541 17925951968964900989453)
                    ·
                      rfl

theorem cell22_52366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_52366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52366 prefixEnd_52366 := by exact prefixLift 52366
  have htrace : WordTrace (prefixWord ++ tailWord_52366) baseStart_52366 baseEnd_52366 := by
    simpa [prefixWord, tailWord_52366, baseEnd_52366] using wordTrace_append hprefix tailTrace_52366
  have hstable : (prefixWord ++ tailWord_52366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52366).length < 2 ^ (prefixWord ++ tailWord_52366).sum := by decide
  have hdescent : baseEnd_52366 < baseStart_52366 := by decide
  rcases family_descends (prefixWord ++ tailWord_52366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52409 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_52409 : Nat := 118140960795 + 52409 * 2 ^ 59
def prefixEnd_52409 : Nat := 4983230072969 + 3 ^ 40 * 52409 * 2
def baseEnd_52409 : Nat := 17940671747727122164321

theorem tailTrace_52409 : CollatzResearch.WordTrace tailWord_52409 prefixEnd_52409 17940671747727122164321 := by
  unfold tailWord_52409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911513267138618589704281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1274342178092412393136187 1911513267138618589704281)
  ·
    refine ⟨1433634950353963942278211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1911513267138618589704281 1433634950353963942278211)
    ·
      refine ⟨2150452425530945913417317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1433634950353963942278211 2150452425530945913417317)
      ·
        refine ⟨403209829787052358765747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2150452425530945913417317 403209829787052358765747)
        ·
          refine ⟨604814744680578538148621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403209829787052358765747 604814744680578538148621)
          ·
            refine ⟨226805529255216951805733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604814744680578538148621 226805529255216951805733)
            ·
              refine ⟨42526036735353178463575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226805529255216951805733 42526036735353178463575)
              ·
                refine ⟨63789055103029767695363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42526036735353178463575 63789055103029767695363)
                ·
                  refine ⟨95683582654544651543045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63789055103029767695363 95683582654544651543045)
                  ·
                    refine ⟨17940671747727122164321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95683582654544651543045 17940671747727122164321)
                    ·
                      rfl

theorem cell22_52409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_52409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52409 prefixEnd_52409 := by exact prefixLift 52409
  have htrace : WordTrace (prefixWord ++ tailWord_52409) baseStart_52409 baseEnd_52409 := by
    simpa [prefixWord, tailWord_52409, baseEnd_52409] using wordTrace_append hprefix tailTrace_52409
  have hstable : (prefixWord ++ tailWord_52409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52409).length < 2 ^ (prefixWord ++ tailWord_52409).sum := by decide
  have hdescent : baseEnd_52409 < baseStart_52409 := by decide
  rcases family_descends (prefixWord ++ tailWord_52409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52437 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_52437 : Nat := 118140960795 + 52437 * 2 ^ 59
def prefixEnd_52437 : Nat := 4983230072969 + 3 ^ 40 * 52437 * 2
def baseEnd_52437 : Nat := 17950256719944382464235

theorem tailTrace_52437 : CollatzResearch.WordTrace tailWord_52437 prefixEnd_52437 17950256719944382464235 := by
  unfold tailWord_52437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912534511037179371723565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1275023007358119581149043 1912534511037179371723565)
  ·
    refine ⟨717200441638942264396337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1912534511037179371723565 717200441638942264396337)
    ·
      refine ⟨537900331229206698297253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717200441638942264396337 537900331229206698297253)
      ·
        refine ⟨100856312105476255930735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537900331229206698297253 100856312105476255930735)
        ·
          refine ⟨151284468158214383896103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100856312105476255930735 151284468158214383896103)
          ·
            refine ⟨226926702237321575844155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151284468158214383896103 226926702237321575844155)
            ·
              refine ⟨340390053355982363766233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226926702237321575844155 340390053355982363766233)
              ·
                refine ⟨255292540016986772824675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340390053355982363766233 255292540016986772824675)
                ·
                  refine ⟨382938810025480159237013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255292540016986772824675 382938810025480159237013)
                  ·
                    refine ⟨17950256719944382464235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 382938810025480159237013 17950256719944382464235)
                    ·
                      rfl

theorem cell22_52437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_52437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52437 prefixEnd_52437 := by exact prefixLift 52437
  have htrace : WordTrace (prefixWord ++ tailWord_52437) baseStart_52437 baseEnd_52437 := by
    simpa [prefixWord, tailWord_52437, baseEnd_52437] using wordTrace_append hprefix tailTrace_52437
  have hstable : (prefixWord ++ tailWord_52437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52437).length < 2 ^ (prefixWord ++ tailWord_52437).sum := by decide
  have hdescent : baseEnd_52437 < baseStart_52437 := by decide
  rcases family_descends (prefixWord ++ tailWord_52437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52452 : List Nat := [2, 3, 1, 1, 1, 2, 6, 6]
def baseStart_52452 : Nat := 118140960795 + 52452 * 2 ^ 59
def prefixEnd_52452 : Nat := 4983230072969 + 3 ^ 40 * 52452 * 2
def baseEnd_52452 : Nat := 1995043502943260371021

theorem tailTrace_52452 : CollatzResearch.WordTrace tailWord_52452 prefixEnd_52452 1995043502943260371021 := by
  unfold tailWord_52452
  simp only [CollatzResearch.WordTrace]
  refine ⟨956540802991418466759805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1275387737321891289013073 956540802991418466759805)
  ·
    refine ⟨358702801121781925034927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 956540802991418466759805 358702801121781925034927)
    ·
      refine ⟨538054201682672887552391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358702801121781925034927 538054201682672887552391)
      ·
        refine ⟨807081302524009331328587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538054201682672887552391 807081302524009331328587)
        ·
          refine ⟨1210621953786013996992881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807081302524009331328587 1210621953786013996992881)
          ·
            refine ⟨907966465339510497744661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210621953786013996992881 907966465339510497744661)
            ·
              refine ⟨42560928062789554581781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 907966465339510497744661 42560928062789554581781)
              ·
                refine ⟨1995043502943260371021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42560928062789554581781 1995043502943260371021)
                ·
                  rfl

theorem cell22_52452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_52452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52452 prefixEnd_52452 := by exact prefixLift 52452
  have htrace : WordTrace (prefixWord ++ tailWord_52452) baseStart_52452 baseEnd_52452 := by
    simpa [prefixWord, tailWord_52452, baseEnd_52452] using wordTrace_append hprefix tailTrace_52452
  have hstable : (prefixWord ++ tailWord_52452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52452).length < 2 ^ (prefixWord ++ tailWord_52452).sum := by decide
  have hdescent : baseEnd_52452 < baseStart_52452 := by decide
  rcases family_descends (prefixWord ++ tailWord_52452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52465 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_52465 : Nat := 118140960795 + 52465 * 2 ^ 59
def prefixEnd_52465 : Nat := 4983230072969 + 3 ^ 40 * 52465 * 2
def baseEnd_52465 : Nat := 17959841692161642764149

theorem tailTrace_52465 : CollatzResearch.WordTrace tailWord_52465 prefixEnd_52465 17959841692161642764149 := by
  unfold tailWord_52465
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913555754935740153742849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1275703836623826769161899 1913555754935740153742849)
  ·
    refine ⟨1435166816201805115307137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1913555754935740153742849 1435166816201805115307137)
    ·
      refine ⟨1076375112151353836480353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1435166816201805115307137 1076375112151353836480353)
      ·
        refine ⟨807281334113515377360265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076375112151353836480353 807281334113515377360265)
        ·
          refine ⟨605461000585136533020199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807281334113515377360265 605461000585136533020199)
          ·
            refine ⟨908191500877704799530299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605461000585136533020199 908191500877704799530299)
            ·
              refine ⟨1362287251316557199295449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908191500877704799530299 1362287251316557199295449)
              ·
                refine ⟨1021715438487417899471587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362287251316557199295449 1021715438487417899471587)
                ·
                  refine ⟨1532573157731126849207381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021715438487417899471587 1532573157731126849207381)
                  ·
                    refine ⟨17959841692161642764149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1532573157731126849207381 17959841692161642764149)
                    ·
                      rfl

theorem cell22_52465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_52465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52465 prefixEnd_52465 := by exact prefixLift 52465
  have htrace : WordTrace (prefixWord ++ tailWord_52465) baseStart_52465 baseEnd_52465 := by
    simpa [prefixWord, tailWord_52465, baseEnd_52465] using wordTrace_append hprefix tailTrace_52465
  have hstable : (prefixWord ++ tailWord_52465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52465).length < 2 ^ (prefixWord ++ tailWord_52465).sum := by decide
  have hdescent : baseEnd_52465 < baseStart_52465 := by decide
  rcases family_descends (prefixWord ++ tailWord_52465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52497 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 5]
def baseStart_52497 : Nat := 118140960795 + 52497 * 2 ^ 59
def prefixEnd_52497 : Nat := 4983230072969 + 3 ^ 40 * 52497 * 2
def baseEnd_52497 : Nat := 5990265315374741988017

theorem tailTrace_52497 : CollatzResearch.WordTrace tailWord_52497 prefixEnd_52497 5990265315374741988017 := by
  unfold tailWord_52497
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914722890819809618907745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1276481927213206412605163 1914722890819809618907745)
  ·
    refine ⟨1436042168114857214180809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1914722890819809618907745 1436042168114857214180809)
    ·
      refine ⟨1077031626086142910635607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436042168114857214180809 1077031626086142910635607)
      ·
        refine ⟨1615547439129214365953411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077031626086142910635607 1615547439129214365953411)
        ·
          refine ⟨2423321158693821548930117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615547439129214365953411 2423321158693821548930117)
          ·
            refine ⟨454372717255091540424397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2423321158693821548930117 454372717255091540424397)
            ·
              refine ⟨170389768970659327659149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454372717255091540424397 170389768970659327659149)
              ·
                refine ⟨63896163363997247872181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170389768970659327659149 63896163363997247872181)
                ·
                  refine ⟨5990265315374741988017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63896163363997247872181 5990265315374741988017)
                  ·
                    rfl

theorem cell22_52497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_52497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52497 prefixEnd_52497 := by exact prefixLift 52497
  have htrace : WordTrace (prefixWord ++ tailWord_52497) baseStart_52497 baseEnd_52497 := by
    simpa [prefixWord, tailWord_52497, baseEnd_52497] using wordTrace_append hprefix tailTrace_52497
  have hstable : (prefixWord ++ tailWord_52497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52497).length < 2 ^ (prefixWord ++ tailWord_52497).sum := by decide
  have hdescent : baseEnd_52497 < baseStart_52497 := by decide
  rcases family_descends (prefixWord ++ tailWord_52497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52576 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_52576 : Nat := 118140960795 + 52576 * 2 ^ 59
def prefixEnd_52576 : Nat := 4983230072969 + 3 ^ 40 * 52576 * 2
def baseEnd_52576 : Nat := 5999279753531451079603

theorem tailTrace_52576 : CollatzResearch.WordTrace tailWord_52576 prefixEnd_52576 5999279753531451079603 := by
  unfold tailWord_52576
  simp only [CollatzResearch.WordTrace]
  refine ⟨958802128766803055516791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1278402838355737407355721 958802128766803055516791)
  ·
    refine ⟨1438203193150204583275187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958802128766803055516791 1438203193150204583275187)
    ·
      refine ⟨2157304789725306874912781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438203193150204583275187 2157304789725306874912781)
      ·
        refine ⟨808989296146990078092293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2157304789725306874912781 808989296146990078092293)
        ·
          refine ⟨151685493027560639642305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 808989296146990078092293 151685493027560639642305)
          ·
            refine ⟨113764119770670479731729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151685493027560639642305 113764119770670479731729)
            ·
              refine ⟨85323089828002859798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113764119770670479731729 85323089828002859798797)
              ·
                refine ⟨31996158685501072424549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85323089828002859798797 31996158685501072424549)
                ·
                  refine ⟨5999279753531451079603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31996158685501072424549 5999279753531451079603)
                  ·
                    rfl

theorem cell22_52576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_52576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52576 prefixEnd_52576 := by exact prefixLift 52576
  have htrace : WordTrace (prefixWord ++ tailWord_52576) baseStart_52576 baseEnd_52576 := by
    simpa [prefixWord, tailWord_52576, baseEnd_52576] using wordTrace_append hprefix tailTrace_52576
  have hstable : (prefixWord ++ tailWord_52576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52576).length < 2 ^ (prefixWord ++ tailWord_52576).sum := by decide
  have hdescent : baseEnd_52576 < baseStart_52576 := by decide
  rcases family_descends (prefixWord ++ tailWord_52576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52619 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 3, 3]
def baseStart_52619 : Nat := 118140960795 + 52619 * 2 ^ 59
def prefixEnd_52619 : Nat := 4983230072969 + 3 ^ 40 * 52619 * 2
def baseEnd_52619 : Nat := 18012559039356574413677

theorem tailTrace_52619 : CollatzResearch.WordTrace tailWord_52619 prefixEnd_52619 18012559039356574413677 := by
  unfold tailWord_52619
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919172596377824454848911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1279448397585216303232607 1919172596377824454848911)
  ·
    refine ⟨2878758894566736682273367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1919172596377824454848911 2878758894566736682273367)
    ·
      refine ⟨4318138341850105023410051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878758894566736682273367 4318138341850105023410051)
      ·
        refine ⟨6477207512775157535115077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318138341850105023410051 6477207512775157535115077)
        ·
          refine ⟨1214476408645342037834077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6477207512775157535115077 1214476408645342037834077)
          ·
            refine ⟨455428653242003264187779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1214476408645342037834077 455428653242003264187779)
            ·
              refine ⟨683142979863004896281669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455428653242003264187779 683142979863004896281669)
              ·
                refine ⟨128089308724313418052813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683142979863004896281669 128089308724313418052813)
                ·
                  refine ⟨48033490771617531769805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128089308724313418052813 48033490771617531769805)
                  ·
                    refine ⟨18012559039356574413677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48033490771617531769805 18012559039356574413677)
                    ·
                      rfl

theorem cell22_52619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 3].length) (baseStart_52619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52619 prefixEnd_52619 := by exact prefixLift 52619
  have htrace : WordTrace (prefixWord ++ tailWord_52619) baseStart_52619 baseEnd_52619 := by
    simpa [prefixWord, tailWord_52619, baseEnd_52619] using wordTrace_append hprefix tailTrace_52619
  have hstable : (prefixWord ++ tailWord_52619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52619).length < 2 ^ (prefixWord ++ tailWord_52619).sum := by decide
  have hdescent : baseEnd_52619 < baseStart_52619 := by decide
  rcases family_descends (prefixWord ++ tailWord_52619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52638 : List Nat := [4, 3, 1, 2, 3, 1, 8]
def baseStart_52638 : Nat := 118140960795 + 52638 * 2 ^ 59
def prefixEnd_52638 : Nat := 4983230072969 + 3 ^ 40 * 52638 * 2
def baseEnd_52638 : Nat := 667372708431365118097

theorem tailTrace_52638 : CollatzResearch.WordTrace tailWord_52638 prefixEnd_52638 667372708431365118097 := by
  unfold tailWord_52638
  simp only [CollatzResearch.WordTrace]
  refine ⟨239983197913623837473821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1279910388872660466527045 239983197913623837473821)
  ·
    refine ⟨89993699217608939052683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239983197913623837473821 89993699217608939052683)
    ·
      refine ⟨134990548826413408579025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89993699217608939052683 134990548826413408579025)
      ·
        refine ⟨101242911619810056434269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134990548826413408579025 101242911619810056434269)
        ·
          refine ⟨37966091857428771162851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101242911619810056434269 37966091857428771162851)
          ·
            refine ⟨56949137786143156744277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37966091857428771162851 56949137786143156744277)
            ·
              refine ⟨667372708431365118097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 56949137786143156744277 667372708431365118097)
              ·
                rfl

theorem cell22_52638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 8].length) (baseStart_52638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52638 prefixEnd_52638 := by exact prefixLift 52638
  have htrace : WordTrace (prefixWord ++ tailWord_52638) baseStart_52638 baseEnd_52638 := by
    simpa [prefixWord, tailWord_52638, baseEnd_52638] using wordTrace_append hprefix tailTrace_52638
  have hstable : (prefixWord ++ tailWord_52638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52638).length < 2 ^ (prefixWord ++ tailWord_52638).sum := by decide
  have hdescent : baseEnd_52638 < baseStart_52638 := by decide
  rcases family_descends (prefixWord ++ tailWord_52638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52653 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_52653 : Nat := 118140960795 + 52653 * 2 ^ 59
def prefixEnd_52653 : Nat := 4983230072969 + 3 ^ 40 * 52653 * 2
def baseEnd_52653 : Nat := 18024197934191819063573

theorem tailTrace_52653 : CollatzResearch.WordTrace tailWord_52653 prefixEnd_52653 18024197934191819063573 := by
  unfold tailWord_52653
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920412678254648261586613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1280275118836432174391075 1920412678254648261586613)
  ·
    refine ⟨180038688586373274523745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1920412678254648261586613 180038688586373274523745)
    ·
      refine ⟨135029016439779955892809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180038688586373274523745 135029016439779955892809)
      ·
        refine ⟨101271762329834966919607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135029016439779955892809 101271762329834966919607)
        ·
          refine ⟨151907643494752450379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101271762329834966919607 151907643494752450379411)
          ·
            refine ⟨227861465242128675569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151907643494752450379411 227861465242128675569117)
            ·
              refine ⟨85448049465798253338419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227861465242128675569117 85448049465798253338419)
              ·
                refine ⟨128172074198697380007629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85448049465798253338419 128172074198697380007629)
                ·
                  refine ⟨48064527824511517502861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128172074198697380007629 48064527824511517502861)
                  ·
                    refine ⟨18024197934191819063573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48064527824511517502861 18024197934191819063573)
                    ·
                      rfl

theorem cell22_52653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_52653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52653 prefixEnd_52653 := by exact prefixLift 52653
  have htrace : WordTrace (prefixWord ++ tailWord_52653) baseStart_52653 baseEnd_52653 := by
    simpa [prefixWord, tailWord_52653, baseEnd_52653] using wordTrace_append hprefix tailTrace_52653
  have hstable : (prefixWord ++ tailWord_52653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52653).length < 2 ^ (prefixWord ++ tailWord_52653).sum := by decide
  have hdescent : baseEnd_52653 < baseStart_52653 := by decide
  rcases family_descends (prefixWord ++ tailWord_52653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52679 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_52679 : Nat := 118140960795 + 52679 * 2 ^ 59
def prefixEnd_52679 : Nat := 4983230072969 + 3 ^ 40 * 52679 * 2
def baseEnd_52679 : Nat := 18033098265536417913493

theorem tailTrace_52679 : CollatzResearch.WordTrace tailWord_52679 prefixEnd_52679 18033098265536417913493 := by
  unfold tailWord_52679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921360976160454702033091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1280907317440303134688727 1921360976160454702033091)
  ·
    refine ⟨2882041464240682053049637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921360976160454702033091 2882041464240682053049637)
    ·
      refine ⟨540382774545127884946807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2882041464240682053049637 540382774545127884946807)
      ·
        refine ⟨810574161817691827420211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540382774545127884946807 810574161817691827420211)
        ·
          refine ⟨1215861242726537741130317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810574161817691827420211 1215861242726537741130317)
          ·
            refine ⟨455947966022451652923869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1215861242726537741130317 455947966022451652923869)
            ·
              refine ⟨170980487258419369846451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 455947966022451652923869 170980487258419369846451)
              ·
                refine ⟨256470730887629054769677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170980487258419369846451 256470730887629054769677)
                ·
                  refine ⟨96176524082860895538629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256470730887629054769677 96176524082860895538629)
                  ·
                    refine ⟨18033098265536417913493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96176524082860895538629 18033098265536417913493)
                    ·
                      rfl

theorem cell22_52679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_52679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52679 prefixEnd_52679 := by exact prefixLift 52679
  have htrace : WordTrace (prefixWord ++ tailWord_52679) baseStart_52679 baseEnd_52679 := by
    simpa [prefixWord, tailWord_52679, baseEnd_52679] using wordTrace_append hprefix tailTrace_52679
  have hstable : (prefixWord ++ tailWord_52679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52679).length < 2 ^ (prefixWord ++ tailWord_52679).sum := by decide
  have hdescent : baseEnd_52679 < baseStart_52679 := by decide
  rcases family_descends (prefixWord ++ tailWord_52679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52726 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_52726 : Nat := 118140960795 + 52726 * 2 ^ 59
def prefixEnd_52726 : Nat := 4983230072969 + 3 ^ 40 * 52726 * 2
def baseEnd_52726 : Nat := 18049187326043961988349

theorem tailTrace_52726 : CollatzResearch.WordTrace tailWord_52726 prefixEnd_52726 18049187326043961988349 := by
  unfold tailWord_52726
  simp only [CollatzResearch.WordTrace]
  refine ⟨120192200436886358062127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1282050137993454485996021 120192200436886358062127)
  ·
    refine ⟨180288300655329537093191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120192200436886358062127 180288300655329537093191)
    ·
      refine ⟨270432450982994305639787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180288300655329537093191 270432450982994305639787)
      ·
        refine ⟨405648676474491458459681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270432450982994305639787 405648676474491458459681)
        ·
          refine ⟨304236507355868593844761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405648676474491458459681 304236507355868593844761)
          ·
            refine ⟨228177380516901445383571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304236507355868593844761 228177380516901445383571)
            ·
              refine ⟨342266070775352168075357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228177380516901445383571 342266070775352168075357)
              ·
                refine ⟨128349776540757063028259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342266070775352168075357 128349776540757063028259)
                ·
                  refine ⟨192524664811135594542389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128349776540757063028259 192524664811135594542389)
                  ·
                    refine ⟨18049187326043961988349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 192524664811135594542389 18049187326043961988349)
                    ·
                      rfl

theorem cell22_52726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_52726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52726 prefixEnd_52726 := by exact prefixLift 52726
  have htrace : WordTrace (prefixWord ++ tailWord_52726) baseStart_52726 baseEnd_52726 := by
    simpa [prefixWord, tailWord_52726, baseEnd_52726] using wordTrace_append hprefix tailTrace_52726
  have hstable : (prefixWord ++ tailWord_52726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52726).length < 2 ^ (prefixWord ++ tailWord_52726).sum := by decide
  have hdescent : baseEnd_52726 < baseStart_52726 := by decide
  rcases family_descends (prefixWord ++ tailWord_52726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52760 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_52760 : Nat := 118140960795 + 52760 * 2 ^ 59
def prefixEnd_52760 : Nat := 4983230072969 + 3 ^ 40 * 52760 * 2
def baseEnd_52760 : Nat := 18060826220879206638245

theorem tailTrace_52760 : CollatzResearch.WordTrace tailWord_52760 prefixEnd_52760 18060826220879206638245 := by
  unfold tailWord_52760
  simp only [CollatzResearch.WordTrace]
  refine ⟨962157644433502767865867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1282876859244670357154489 962157644433502767865867)
  ·
    refine ⟨1443236466650254151798801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962157644433502767865867 1443236466650254151798801)
    ·
      refine ⟨1082427349987690613849101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1443236466650254151798801 1082427349987690613849101)
      ·
        refine ⟨405910256245383980193413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1082427349987690613849101 405910256245383980193413)
        ·
          refine ⟨76108173046009496286265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405910256245383980193413 76108173046009496286265)
          ·
            refine ⟨57081129784507122214699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76108173046009496286265 57081129784507122214699)
            ·
              refine ⟨85621694676760683322049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57081129784507122214699 85621694676760683322049)
              ·
                refine ⟨64216271007570512491537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85621694676760683322049 64216271007570512491537)
                ·
                  refine ⟨48162203255677884368653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64216271007570512491537 48162203255677884368653)
                  ·
                    refine ⟨18060826220879206638245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48162203255677884368653 18060826220879206638245)
                    ·
                      rfl

theorem cell22_52760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_52760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52760 prefixEnd_52760 := by exact prefixLift 52760
  have htrace : WordTrace (prefixWord ++ tailWord_52760) baseStart_52760 baseEnd_52760 := by
    simpa [prefixWord, tailWord_52760, baseEnd_52760] using wordTrace_append hprefix tailTrace_52760
  have hstable : (prefixWord ++ tailWord_52760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52760).length < 2 ^ (prefixWord ++ tailWord_52760).sum := by decide
  have hdescent : baseEnd_52760 < baseStart_52760 := by decide
  rcases family_descends (prefixWord ++ tailWord_52760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52790 : List Nat := [5, 1, 2, 1, 3, 2, 2, 6]
def baseStart_52790 : Nat := 118140960795 + 52790 * 2 ^ 59
def prefixEnd_52790 : Nat := 4983230072969 + 3 ^ 40 * 52790 * 2
def baseEnd_52790 : Nat := 2007899537107680932017

theorem tailTrace_52790 : CollatzResearch.WordTrace tailWord_52790 prefixEnd_52790 2007899537107680932017 := by
  unfold tailWord_52790
  simp only [CollatzResearch.WordTrace]
  refine ⟨120338092422395041207739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1283606319172213772882549 120338092422395041207739)
  ·
    refine ⟨180507138633592561811609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120338092422395041207739 180507138633592561811609)
    ·
      refine ⟨135380353975194421358707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180507138633592561811609 135380353975194421358707)
      ·
        refine ⟨203070530962791632038061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135380353975194421358707 203070530962791632038061)
        ·
          refine ⟨76151449111046862014273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203070530962791632038061 76151449111046862014273)
          ·
            refine ⟨57113586833285146510705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76151449111046862014273 57113586833285146510705)
            ·
              refine ⟨42835190124963859883029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57113586833285146510705 42835190124963859883029)
              ·
                refine ⟨2007899537107680932017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42835190124963859883029 2007899537107680932017)
                ·
                  rfl

theorem cell22_52790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_52790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52790 prefixEnd_52790 := by exact prefixLift 52790
  have htrace : WordTrace (prefixWord ++ tailWord_52790) baseStart_52790 baseEnd_52790 := by
    simpa [prefixWord, tailWord_52790, baseEnd_52790] using wordTrace_append hprefix tailTrace_52790
  have hstable : (prefixWord ++ tailWord_52790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52790).length < 2 ^ (prefixWord ++ tailWord_52790).sum := by decide
  have hdescent : baseEnd_52790 < baseStart_52790 := by decide
  rcases family_descends (prefixWord ++ tailWord_52790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52848 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_52848 : Nat := 118140960795 + 52848 * 2 ^ 59
def prefixEnd_52848 : Nat := 4983230072969 + 3 ^ 40 * 52848 * 2
def baseEnd_52848 : Nat := 18090950419276310437975

theorem tailTrace_52848 : CollatzResearch.WordTrace tailWord_52848 prefixEnd_52848 18090950419276310437975 := by
  unfold tailWord_52848
  simp only [CollatzResearch.WordTrace]
  refine ⟨963762456274098282467599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1285016608365464376623465 963762456274098282467599)
  ·
    refine ⟨1445643684411147423701399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 963762456274098282467599 1445643684411147423701399)
    ·
      refine ⟨2168465526616721135552099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1445643684411147423701399 2168465526616721135552099)
      ·
        refine ⟨3252698289925081703328149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168465526616721135552099 3252698289925081703328149)
        ·
          refine ⟨152470232340238204843507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3252698289925081703328149 152470232340238204843507)
          ·
            refine ⟨228705348510357307265261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152470232340238204843507 228705348510357307265261)
            ·
              refine ⟨85764505691383990224473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228705348510357307265261 85764505691383990224473)
              ·
                refine ⟨64323379268537992668355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85764505691383990224473 64323379268537992668355)
                ·
                  refine ⟨96485068902806989002533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64323379268537992668355 96485068902806989002533)
                  ·
                    refine ⟨18090950419276310437975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96485068902806989002533 18090950419276310437975)
                    ·
                      rfl

theorem cell22_52848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_52848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52848 prefixEnd_52848 := by exact prefixLift 52848
  have htrace : WordTrace (prefixWord ++ tailWord_52848) baseStart_52848 baseEnd_52848 := by
    simpa [prefixWord, tailWord_52848, baseEnd_52848] using wordTrace_append hprefix tailTrace_52848
  have hstable : (prefixWord ++ tailWord_52848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52848).length < 2 ^ (prefixWord ++ tailWord_52848).sum := by decide
  have hdescent : baseEnd_52848 < baseStart_52848 := by decide
  rcases family_descends (prefixWord ++ tailWord_52848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52861 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_52861 : Nat := 118140960795 + 52861 * 2 ^ 59
def prefixEnd_52861 : Nat := 4983230072969 + 3 ^ 40 * 52861 * 2
def baseEnd_52861 : Nat := 18095400584948609862935

theorem tailTrace_52861 : CollatzResearch.WordTrace tailWord_52861 prefixEnd_52861 18095400584948609862935 := by
  unfold tailWord_52861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927999061501099785158437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1285332707667399856772291 1927999061501099785158437)
  ·
    refine ⟨361499824031456209717207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1927999061501099785158437 361499824031456209717207)
    ·
      refine ⟨542249736047184314575811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361499824031456209717207 542249736047184314575811)
      ·
        refine ⟨813374604070776471863717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542249736047184314575811 813374604070776471863717)
        ·
          refine ⟨152507738263270588474447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 813374604070776471863717 152507738263270588474447)
          ·
            refine ⟨228761607394905882711671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152507738263270588474447 228761607394905882711671)
            ·
              refine ⟨343142411092358824067507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228761607394905882711671 343142411092358824067507)
              ·
                refine ⟨514713616638538236101261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343142411092358824067507 514713616638538236101261)
                ·
                  refine ⟨193017606239451838537973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 514713616638538236101261 193017606239451838537973)
                  ·
                    refine ⟨18095400584948609862935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193017606239451838537973 18095400584948609862935)
                    ·
                      rfl

theorem cell22_52861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_52861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52861 prefixEnd_52861 := by exact prefixLift 52861
  have htrace : WordTrace (prefixWord ++ tailWord_52861) baseStart_52861 baseEnd_52861 := by
    simpa [prefixWord, tailWord_52861, baseEnd_52861] using wordTrace_append hprefix tailTrace_52861
  have hstable : (prefixWord ++ tailWord_52861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52861).length < 2 ^ (prefixWord ++ tailWord_52861).sum := by decide
  have hdescent : baseEnd_52861 < baseStart_52861 := by decide
  rcases family_descends (prefixWord ++ tailWord_52861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52865 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_52865 : Nat := 118140960795 + 52865 * 2 ^ 59
def prefixEnd_52865 : Nat := 4983230072969 + 3 ^ 40 * 52865 * 2
def baseEnd_52865 : Nat := 18096769866693932762923

theorem tailTrace_52865 : CollatzResearch.WordTrace tailWord_52865 prefixEnd_52865 18096769866693932762923 := by
  unfold tailWord_52865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928144953486608468304049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1285429968991072312202699 1928144953486608468304049)
  ·
    refine ⟨1446108715114956351228037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928144953486608468304049 1446108715114956351228037)
    ·
      refine ⟨271145384084054315855257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1446108715114956351228037 271145384084054315855257)
      ·
        refine ⟨203359038063040736891443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271145384084054315855257 203359038063040736891443)
        ·
          refine ⟨305038557094561105337165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203359038063040736891443 305038557094561105337165)
          ·
            refine ⟨114389458910460414501437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305038557094561105337165 114389458910460414501437)
            ·
              refine ⟨42896047091422655438039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114389458910460414501437 42896047091422655438039)
              ·
                refine ⟨64344070637133983157059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42896047091422655438039 64344070637133983157059)
                ·
                  refine ⟨96516105955700974735589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64344070637133983157059 96516105955700974735589)
                  ·
                    refine ⟨18096769866693932762923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96516105955700974735589 18096769866693932762923)
                    ·
                      rfl

theorem cell22_52865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_52865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52865 prefixEnd_52865 := by exact prefixLift 52865
  have htrace : WordTrace (prefixWord ++ tailWord_52865) baseStart_52865 baseEnd_52865 := by
    simpa [prefixWord, tailWord_52865, baseEnd_52865] using wordTrace_append hprefix tailTrace_52865
  have hstable : (prefixWord ++ tailWord_52865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52865).length < 2 ^ (prefixWord ++ tailWord_52865).sum := by decide
  have hdescent : baseEnd_52865 < baseStart_52865 := by decide
  rcases family_descends (prefixWord ++ tailWord_52865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52876 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_52876 : Nat := 118140960795 + 52876 * 2 ^ 59
def prefixEnd_52876 : Nat := 4983230072969 + 3 ^ 40 * 52876 * 2
def baseEnd_52876 : Nat := 18100535391493570737889

theorem tailTrace_52876 : CollatzResearch.WordTrace tailWord_52876 prefixEnd_52876 18100535391493570737889 := by
  unfold tailWord_52876
  simp only [CollatzResearch.WordTrace]
  refine ⟨964273078223378673477241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1285697437631171564636321 964273078223378673477241)
  ·
    refine ⟨723204808667534005107931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 964273078223378673477241 723204808667534005107931)
    ·
      refine ⟨1084807213001301007661897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723204808667534005107931 1084807213001301007661897)
      ·
        refine ⟨813605409750975755746423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084807213001301007661897 813605409750975755746423)
        ·
          refine ⟨1220408114626463633619635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813605409750975755746423 1220408114626463633619635)
          ·
            refine ⟨1830612171939695450429453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220408114626463633619635 1830612171939695450429453)
            ·
              refine ⟨686479564477385793911045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1830612171939695450429453 686479564477385793911045)
              ·
                refine ⟨128714918339509836358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 686479564477385793911045 128714918339509836358321)
                ·
                  refine ⟨96536188754632377268741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128714918339509836358321 96536188754632377268741)
                  ·
                    refine ⟨18100535391493570737889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96536188754632377268741 18100535391493570737889)
                    ·
                      rfl

theorem cell22_52876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_52876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52876 prefixEnd_52876 := by exact prefixLift 52876
  have htrace : WordTrace (prefixWord ++ tailWord_52876) baseStart_52876 baseEnd_52876 := by
    simpa [prefixWord, tailWord_52876, baseEnd_52876] using wordTrace_append hprefix tailTrace_52876
  have hstable : (prefixWord ++ tailWord_52876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52876).length < 2 ^ (prefixWord ++ tailWord_52876).sum := by decide
  have hdescent : baseEnd_52876 < baseStart_52876 := by decide
  rcases family_descends (prefixWord ++ tailWord_52876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52895 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 1, 5]
def baseStart_52895 : Nat := 118140960795 + 52895 * 2 ^ 59
def prefixEnd_52895 : Nat := 4983230072969 + 3 ^ 40 * 52895 * 2
def baseEnd_52895 : Nat := 18107039479783854512831

theorem tailTrace_52895 : CollatzResearch.WordTrace tailWord_52895 prefixEnd_52895 18107039479783854512831 := by
  unfold tailWord_52895
  simp only [CollatzResearch.WordTrace]
  refine ⟨1929239143377923591896139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1286159428918615727930759 1929239143377923591896139)
  ·
    refine ⟨2893858715066885387844209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1929239143377923591896139 2893858715066885387844209)
    ·
      refine ⟨2170394036300164040883157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2893858715066885387844209 2170394036300164040883157)
      ·
        refine ⟨50868610225785094708199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2170394036300164040883157 50868610225785094708199)
        ·
          refine ⟨76302915338677642062299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50868610225785094708199 76302915338677642062299)
          ·
            refine ⟨114454373008016463093449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76302915338677642062299 114454373008016463093449)
            ·
              refine ⟨85840779756012347320087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114454373008016463093449 85840779756012347320087)
              ·
                refine ⟨128761169634018520980131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85840779756012347320087 128761169634018520980131)
                ·
                  refine ⟨193141754451027781470197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128761169634018520980131 193141754451027781470197)
                  ·
                    refine ⟨18107039479783854512831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193141754451027781470197 18107039479783854512831)
                    ·
                      rfl

theorem cell22_52895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 5].length) (baseStart_52895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52895 prefixEnd_52895 := by exact prefixLift 52895
  have htrace : WordTrace (prefixWord ++ tailWord_52895) baseStart_52895 baseEnd_52895 := by
    simpa [prefixWord, tailWord_52895, baseEnd_52895] using wordTrace_append hprefix tailTrace_52895
  have hstable : (prefixWord ++ tailWord_52895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52895).length < 2 ^ (prefixWord ++ tailWord_52895).sum := by decide
  have hdescent : baseEnd_52895 < baseStart_52895 := by decide
  rcases family_descends (prefixWord ++ tailWord_52895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52910 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_52910 : Nat := 118140960795 + 52910 * 2 ^ 59
def prefixEnd_52910 : Nat := 4983230072969 + 3 ^ 40 * 52910 * 2
def baseEnd_52910 : Nat := 18112174286328815387785

theorem tailTrace_52910 : CollatzResearch.WordTrace tailWord_52910 prefixEnd_52910 18112174286328815387785 := by
  unfold tailWord_52910
  simp only [CollatzResearch.WordTrace]
  refine ⟨241223279790447644211523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1286524158882387435794789 241223279790447644211523)
  ·
    refine ⟨361834919685671466317285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241223279790447644211523 361834919685671466317285)
    ·
      refine ⟨67844047441063399934491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361834919685671466317285 67844047441063399934491)
      ·
        refine ⟨101766071161595099901737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67844047441063399934491 101766071161595099901737)
        ·
          refine ⟨76324553371196324926303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101766071161595099901737 76324553371196324926303)
          ·
            refine ⟨114486830056794487389455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76324553371196324926303 114486830056794487389455)
            ·
              refine ⟨171730245085191731084183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114486830056794487389455 171730245085191731084183)
              ·
                refine ⟨257595367627787596626275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171730245085191731084183 257595367627787596626275)
                ·
                  refine ⟨386393051441681394939413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257595367627787596626275 386393051441681394939413)
                  ·
                    refine ⟨18112174286328815387785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 386393051441681394939413 18112174286328815387785)
                    ·
                      rfl

theorem cell22_52910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_52910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52910 prefixEnd_52910 := by exact prefixLift 52910
  have htrace : WordTrace (prefixWord ++ tailWord_52910) baseStart_52910 baseEnd_52910 := by
    simpa [prefixWord, tailWord_52910, baseEnd_52910] using wordTrace_append hprefix tailTrace_52910
  have hstable : (prefixWord ++ tailWord_52910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52910).length < 2 ^ (prefixWord ++ tailWord_52910).sum := by decide
  have hdescent : baseEnd_52910 < baseStart_52910 := by decide
  rcases family_descends (prefixWord ++ tailWord_52910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52936 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_52936 : Nat := 118140960795 + 52936 * 2 ^ 59
def prefixEnd_52936 : Nat := 4983230072969 + 3 ^ 40 * 52936 * 2
def baseEnd_52936 : Nat := 6040358205891138079235

theorem tailTrace_52936 : CollatzResearch.WordTrace tailWord_52936 prefixEnd_52936 6040358205891138079235 := by
  unfold tailWord_52936
  simp only [CollatzResearch.WordTrace]
  refine ⟨965367268114693797069331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1287156357486258396092441 965367268114693797069331)
  ·
    refine ⟨1448050902172040695603997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 965367268114693797069331 1448050902172040695603997)
    ·
      refine ⟨543019088314515260851499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1448050902172040695603997 543019088314515260851499)
      ·
        refine ⟨814528632471772891277249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543019088314515260851499 814528632471772891277249)
        ·
          refine ⟨610896474353829668457937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814528632471772891277249 610896474353829668457937)
          ·
            refine ⟨458172355765372251343453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610896474353829668457937 458172355765372251343453)
            ·
              refine ⟨171814633412014594253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458172355765372251343453 171814633412014594253795)
              ·
                refine ⟨257721950118021891380693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171814633412014594253795 257721950118021891380693)
                ·
                  refine ⟨6040358205891138079235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 257721950118021891380693 6040358205891138079235)
                  ·
                    rfl

theorem cell22_52936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_52936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52936 prefixEnd_52936 := by exact prefixLift 52936
  have htrace : WordTrace (prefixWord ++ tailWord_52936) baseStart_52936 baseEnd_52936 := by
    simpa [prefixWord, tailWord_52936, baseEnd_52936] using wordTrace_append hprefix tailTrace_52936
  have hstable : (prefixWord ++ tailWord_52936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52936).length < 2 ^ (prefixWord ++ tailWord_52936).sum := by decide
  have hdescent : baseEnd_52936 < baseStart_52936 := by decide
  rcases family_descends (prefixWord ++ tailWord_52936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52951 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_52951 : Nat := 118140960795 + 52951 * 2 ^ 59
def prefixEnd_52951 : Nat := 4983230072969 + 3 ^ 40 * 52951 * 2
def baseEnd_52951 : Nat := 18126209424218375112659

theorem tailTrace_52951 : CollatzResearch.WordTrace tailWord_52951 prefixEnd_52951 18126209424218375112659 := by
  unfold tailWord_52951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931281631175045155934707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1287521087450030103956471 1931281631175045155934707)
  ·
    refine ⟨2896922446762567733902061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1931281631175045155934707 2896922446762567733902061)
    ·
      refine ⟨1086345917535962900213273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2896922446762567733902061 1086345917535962900213273)
      ·
        refine ⟨814759438151972175159955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086345917535962900213273 814759438151972175159955)
        ·
          refine ⟨1222139157227958262739933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814759438151972175159955 1222139157227958262739933)
          ·
            refine ⟨458302183960484348527475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222139157227958262739933 458302183960484348527475)
            ·
              refine ⟨687453275940726522791213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458302183960484348527475 687453275940726522791213)
              ·
                refine ⟨257794978477772446046705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687453275940726522791213 257794978477772446046705)
                ·
                  refine ⟨193346233858329334535029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257794978477772446046705 193346233858329334535029)
                  ·
                    refine ⟨18126209424218375112659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193346233858329334535029 18126209424218375112659)
                    ·
                      rfl

theorem cell22_52951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_52951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52951 prefixEnd_52951 := by exact prefixLift 52951
  have htrace : WordTrace (prefixWord ++ tailWord_52951) baseStart_52951 baseEnd_52951 := by
    simpa [prefixWord, tailWord_52951, baseEnd_52951] using wordTrace_append hprefix tailTrace_52951
  have hstable : (prefixWord ++ tailWord_52951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52951).length < 2 ^ (prefixWord ++ tailWord_52951).sum := by decide
  have hdescent : baseEnd_52951 < baseStart_52951 := by decide
  rcases family_descends (prefixWord ++ tailWord_52951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52983 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 1, 4]
def baseStart_52983 : Nat := 118140960795 + 52983 * 2 ^ 59
def prefixEnd_52983 : Nat := 4983230072969 + 3 ^ 40 * 52983 * 2
def baseEnd_52983 : Nat := 18137163678180958312561

theorem tailTrace_52983 : CollatzResearch.WordTrace tailWord_52983 prefixEnd_52983 18137163678180958312561 := by
  unfold tailWord_52983
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932448767059114621099603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1288299178039409747399735 1932448767059114621099603)
  ·
    refine ⟨2898673150588671931649405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1932448767059114621099603 2898673150588671931649405)
    ·
      refine ⟨1087002431470751974368527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2898673150588671931649405 1087002431470751974368527)
      ·
        refine ⟨1630503647206127961552791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1087002431470751974368527 1630503647206127961552791)
        ·
          refine ⟨2445755470809191942329187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630503647206127961552791 2445755470809191942329187)
          ·
            refine ⟨3668633206213787913493781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445755470809191942329187 3668633206213787913493781)
            ·
              refine ⟨171967181541271308445021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3668633206213787913493781 171967181541271308445021)
              ·
                refine ⟨64487693077976740666883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171967181541271308445021 64487693077976740666883)
                ·
                  refine ⟨96731539616965111000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64487693077976740666883 96731539616965111000325)
                  ·
                    refine ⟨18137163678180958312561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96731539616965111000325 18137163678180958312561)
                    ·
                      rfl

theorem cell22_52983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_52983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_52983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_52983 prefixEnd_52983 := by exact prefixLift 52983
  have htrace : WordTrace (prefixWord ++ tailWord_52983) baseStart_52983 baseEnd_52983 := by
    simpa [prefixWord, tailWord_52983, baseEnd_52983] using wordTrace_append hprefix tailTrace_52983
  have hstable : (prefixWord ++ tailWord_52983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52983).length < 2 ^ (prefixWord ++ tailWord_52983).sum := by decide
  have hdescent : baseEnd_52983 < baseStart_52983 := by decide
  rcases family_descends (prefixWord ++ tailWord_52983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53011 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_53011 : Nat := 118140960795 + 53011 * 2 ^ 59
def prefixEnd_53011 : Nat := 4983230072969 + 3 ^ 40 * 53011 * 2
def baseEnd_53011 : Nat := 18146748650398218612475

theorem tailTrace_53011 : CollatzResearch.WordTrace tailWord_53011 prefixEnd_53011 18146748650398218612475 := by
  unfold tailWord_53011
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933470010957675403118887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1288980007305116935412591 1933470010957675403118887)
  ·
    refine ⟨2900205016436513104678331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1933470010957675403118887 2900205016436513104678331)
    ·
      refine ⟨4350307524654769657017497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900205016436513104678331 4350307524654769657017497)
      ·
        refine ⟨3262730643491077242763123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4350307524654769657017497 3262730643491077242763123)
        ·
          refine ⟨4894095965236615864144685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262730643491077242763123 4894095965236615864144685)
          ·
            refine ⟨1835285986963730949054257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4894095965236615864144685 1835285986963730949054257)
            ·
              refine ⟨1376464490222798211790693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835285986963730949054257 1376464490222798211790693)
              ·
                refine ⟨258087091916774664710755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1376464490222798211790693 258087091916774664710755)
                ·
                  refine ⟨387130637875161997066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258087091916774664710755 387130637875161997066133)
                  ·
                    refine ⟨18146748650398218612475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 387130637875161997066133 18146748650398218612475)
                    ·
                      rfl

theorem cell22_53011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_53011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53011 prefixEnd_53011 := by exact prefixLift 53011
  have htrace : WordTrace (prefixWord ++ tailWord_53011) baseStart_53011 baseEnd_53011 := by
    simpa [prefixWord, tailWord_53011, baseEnd_53011] using wordTrace_append hprefix tailTrace_53011
  have hstable : (prefixWord ++ tailWord_53011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53011).length < 2 ^ (prefixWord ++ tailWord_53011).sum := by decide
  have hdescent : baseEnd_53011 < baseStart_53011 := by decide
  rcases family_descends (prefixWord ++ tailWord_53011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53043 : List Nat := [1, 1, 1, 2, 8, 9]
def baseStart_53043 : Nat := 118140960795 + 53043 * 2 ^ 59
def prefixEnd_53043 : Nat := 4983230072969 + 3 ^ 40 * 53043 * 2
def baseEnd_53043 : Nat := 224169171658775331017

theorem tailTrace_53043 : CollatzResearch.WordTrace tailWord_53043 prefixEnd_53043 224169171658775331017 := by
  unfold tailWord_53043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934637146841744868283783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1289758097894496578855855 1934637146841744868283783)
  ·
    refine ⟨2901955720262617302425675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1934637146841744868283783 2901955720262617302425675)
    ·
      refine ⟨4352933580393925953638513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901955720262617302425675 4352933580393925953638513)
      ·
        refine ⟨3264700185295444465228885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4352933580393925953638513 3264700185295444465228885)
        ·
          refine ⟨38258205296430989826901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 3264700185295444465228885 38258205296430989826901)
          ·
            refine ⟨224169171658775331017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 38258205296430989826901 224169171658775331017)
            ·
              rfl

theorem cell22_53043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 9].length) (baseStart_53043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53043 prefixEnd_53043 := by exact prefixLift 53043
  have htrace : WordTrace (prefixWord ++ tailWord_53043) baseStart_53043 baseEnd_53043 := by
    simpa [prefixWord, tailWord_53043, baseEnd_53043] using wordTrace_append hprefix tailTrace_53043
  have hstable : (prefixWord ++ tailWord_53043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53043).length < 2 ^ (prefixWord ++ tailWord_53043).sum := by decide
  have hdescent : baseEnd_53043 < baseStart_53043 := by decide
  rcases family_descends (prefixWord ++ tailWord_53043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53167 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 4]
def baseStart_53167 : Nat := 118140960795 + 53167 * 2 ^ 59
def prefixEnd_53167 : Nat := 4983230072969 + 3 ^ 40 * 53167 * 2
def baseEnd_53167 : Nat := 6066716879488603903999

theorem tailTrace_53167 : CollatzResearch.WordTrace tailWord_53167 prefixEnd_53167 6066716879488603903999 := by
  unfold tailWord_53167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939159798392514045797755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1292773198928342697198503 1939159798392514045797755)
  ·
    refine ⟨2908739697588771068696633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939159798392514045797755 2908739697588771068696633)
    ·
      refine ⟨2181554773191578301522475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2908739697588771068696633 2181554773191578301522475)
      ·
        refine ⟨3272332159787367452283713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181554773191578301522475 3272332159787367452283713)
        ·
          refine ⟨2454249119840525589212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272332159787367452283713 2454249119840525589212785)
          ·
            refine ⟨1840686839880394191909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454249119840525589212785 1840686839880394191909589)
            ·
              refine ⟨43141097809696738872881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1840686839880394191909589 43141097809696738872881)
              ·
                refine ⟨32355823357272554154661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43141097809696738872881 32355823357272554154661)
                ·
                  refine ⟨6066716879488603903999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32355823357272554154661 6066716879488603903999)
                  ·
                    rfl

theorem cell22_53167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 4].length) (baseStart_53167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53167 prefixEnd_53167 := by exact prefixLift 53167
  have htrace : WordTrace (prefixWord ++ tailWord_53167) baseStart_53167 baseEnd_53167 := by
    simpa [prefixWord, tailWord_53167, baseEnd_53167] using wordTrace_append hprefix tailTrace_53167
  have hstable : (prefixWord ++ tailWord_53167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53167).length < 2 ^ (prefixWord ++ tailWord_53167).sum := by decide
  have hdescent : baseEnd_53167 < baseStart_53167 := by decide
  rcases family_descends (prefixWord ++ tailWord_53167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53212 : List Nat := [2, 2, 6, 1, 11]
def baseStart_53212 : Nat := 118140960795 + 53212 * 2 ^ 59
def prefixEnd_53212 : Nat := 4983230072969 + 3 ^ 40 * 53212 * 2
def baseEnd_53212 : Nat := 74961131926340305913

theorem tailTrace_53212 : CollatzResearch.WordTrace tailWord_53212 prefixEnd_53212 74961131926340305913 := by
  unfold tailWord_53212
  simp only [CollatzResearch.WordTrace]
  refine ⟨970400541614743365592945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1293867388819657820790593 970400541614743365592945)
  ·
    refine ⟨727800406211057524194709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970400541614743365592945 727800406211057524194709)
    ·
      refine ⟨34115644041143321446627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 727800406211057524194709 34115644041143321446627)
      ·
        refine ⟨51173466061714982169941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34115644041143321446627 51173466061714982169941)
        ·
          refine ⟨74961131926340305913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 51173466061714982169941 74961131926340305913)
          ·
            rfl

theorem cell22_53212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 11].length) (baseStart_53212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53212 prefixEnd_53212 := by exact prefixLift 53212
  have htrace : WordTrace (prefixWord ++ tailWord_53212) baseStart_53212 baseEnd_53212 := by
    simpa [prefixWord, tailWord_53212, baseEnd_53212] using wordTrace_append hprefix tailTrace_53212
  have hstable : (prefixWord ++ tailWord_53212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53212).length < 2 ^ (prefixWord ++ tailWord_53212).sum := by decide
  have hdescent : baseEnd_53212 < baseStart_53212 := by decide
  rcases family_descends (prefixWord ++ tailWord_53212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53218 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_53218 : Nat := 118140960795 + 53218 * 2 ^ 59
def prefixEnd_53218 : Nat := 4983230072969 + 3 ^ 40 * 53218 * 2
def baseEnd_53218 : Nat := 6072536326906226228947

theorem tailTrace_53218 : CollatzResearch.WordTrace tailWord_53218 prefixEnd_53218 6072536326906226228947 := by
  unfold tailWord_53218
  simp only [CollatzResearch.WordTrace]
  refine ⟨485254980301937438976077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1294013280805166503936205 485254980301937438976077)
  ·
    refine ⟨181970617613226539616029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 485254980301937438976077 181970617613226539616029)
    ·
      refine ⟨68238981604959952356011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181970617613226539616029 68238981604959952356011)
      ·
        refine ⟨102358472407439928534017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68238981604959952356011 102358472407439928534017)
        ·
          refine ⟨76768854305579946400513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102358472407439928534017 76768854305579946400513)
          ·
            refine ⟨57576640729184959800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76768854305579946400513 57576640729184959800385)
            ·
              refine ⟨43182480546888719850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57576640729184959800385 43182480546888719850289)
              ·
                refine ⟨32386860410166539887717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43182480546888719850289 32386860410166539887717)
                ·
                  refine ⟨6072536326906226228947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32386860410166539887717 6072536326906226228947)
                  ·
                    rfl

theorem cell22_53218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_53218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53218 prefixEnd_53218 := by exact prefixLift 53218
  have htrace : WordTrace (prefixWord ++ tailWord_53218) baseStart_53218 baseEnd_53218 := by
    simpa [prefixWord, tailWord_53218, baseEnd_53218] using wordTrace_append hprefix tailTrace_53218
  have hstable : (prefixWord ++ tailWord_53218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53218).length < 2 ^ (prefixWord ++ tailWord_53218).sum := by decide
  have hdescent : baseEnd_53218 < baseStart_53218 := by decide
  rcases family_descends (prefixWord ++ tailWord_53218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53229 : List Nat := [1, 5, 1, 4, 1, 2, 1, 7]
def baseStart_53229 : Nat := 118140960795 + 53229 * 2 ^ 59
def prefixEnd_53229 : Nat := 4983230072969 + 3 ^ 40 * 53229 * 2
def baseEnd_53229 : Nat := 2024597167279812962423

theorem tailTrace_53229 : CollatzResearch.WordTrace tailWord_53229 prefixEnd_53229 2024597167279812962423 := by
  unfold tailWord_53229
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941421124167898634554741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1294280749445265756369827 1941421124167898634554741)
  ·
    refine ⟨182008230390740496989507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1941421124167898634554741 182008230390740496989507)
    ·
      refine ⟨273012345586110745484261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182008230390740496989507 273012345586110745484261)
      ·
        refine ⟨51189814797395764778299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273012345586110745484261 51189814797395764778299)
        ·
          refine ⟨76784722196093647167449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51189814797395764778299 76784722196093647167449)
          ·
            refine ⟨57588541647070235375587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76784722196093647167449 57588541647070235375587)
            ·
              refine ⟨86382812470605353063381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57588541647070235375587 86382812470605353063381)
              ·
                refine ⟨2024597167279812962423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86382812470605353063381 2024597167279812962423)
                ·
                  rfl

theorem cell22_53229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 7].length) (baseStart_53229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53229 prefixEnd_53229 := by exact prefixLift 53229
  have htrace : WordTrace (prefixWord ++ tailWord_53229) baseStart_53229 baseEnd_53229 := by
    simpa [prefixWord, tailWord_53229, baseEnd_53229] using wordTrace_append hprefix tailTrace_53229
  have hstable : (prefixWord ++ tailWord_53229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53229).length < 2 ^ (prefixWord ++ tailWord_53229).sum := by decide
  have hdescent : baseEnd_53229 < baseStart_53229 := by decide
  rcases family_descends (prefixWord ++ tailWord_53229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53240 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_53240 : Nat := 118140960795 + 53240 * 2 ^ 59
def prefixEnd_53240 : Nat := 4983230072969 + 3 ^ 40 * 53240 * 2
def baseEnd_53240 : Nat := 6075046676772651545591

theorem tailTrace_53240 : CollatzResearch.WordTrace tailWord_53240 prefixEnd_53240 6075046676772651545591 := by
  unfold tailWord_53240
  simp only [CollatzResearch.WordTrace]
  refine ⟨970911163564023756602587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1294548218085365008803449 970911163564023756602587)
  ·
    refine ⟨1456366745346035634903881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970911163564023756602587 1456366745346035634903881)
    ·
      refine ⟨1092275059009526726177911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456366745346035634903881 1092275059009526726177911)
      ·
        refine ⟨1638412588514290089266867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092275059009526726177911 1638412588514290089266867)
        ·
          refine ⟨2457618882771435133900301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638412588514290089266867 2457618882771435133900301)
          ·
            refine ⟨921607081039288175212613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2457618882771435133900301 921607081039288175212613)
            ·
              refine ⟨172801327694866532852365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 921607081039288175212613 172801327694866532852365)
              ·
                refine ⟨64800497885574949819637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172801327694866532852365 64800497885574949819637)
                ·
                  refine ⟨6075046676772651545591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64800497885574949819637 6075046676772651545591)
                  ·
                    rfl

theorem cell22_53240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_53240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53240 prefixEnd_53240 := by exact prefixLift 53240
  have htrace : WordTrace (prefixWord ++ tailWord_53240) baseStart_53240 baseEnd_53240 := by
    simpa [prefixWord, tailWord_53240, baseEnd_53240] using wordTrace_append hprefix tailTrace_53240
  have hstable : (prefixWord ++ tailWord_53240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53240).length < 2 ^ (prefixWord ++ tailWord_53240).sum := by decide
  have hdescent : baseEnd_53240 < baseStart_53240 := by decide
  rcases family_descends (prefixWord ++ tailWord_53240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53285 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 6]
def baseStart_53285 : Nat := 118140960795 + 53285 * 2 ^ 59
def prefixEnd_53285 : Nat := 4983230072969 + 3 ^ 40 * 53285 * 2
def baseEnd_53285 : Nat := 6080181483317612420545

theorem tailTrace_53285 : CollatzResearch.WordTrace tailWord_53285 prefixEnd_53285 6080181483317612420545 := by
  unfold tailWord_53285
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943463611965020198593309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1295642407976680132395539 1943463611965020198593309)
  ·
    refine ⟨728798854486882574472491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1943463611965020198593309 728798854486882574472491)
    ·
      refine ⟨1093198281730323861708737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728798854486882574472491 1093198281730323861708737)
      ·
        refine ⟨819898711297742896281553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093198281730323861708737 819898711297742896281553)
        ·
          refine ⟨614924033473307172211165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819898711297742896281553 614924033473307172211165)
          ·
            refine ⟨230596512552490189579187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614924033473307172211165 230596512552490189579187)
            ·
              refine ⟨345894768828735284368781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230596512552490189579187 345894768828735284368781)
              ·
                refine ⟨129710538310775731638293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345894768828735284368781 129710538310775731638293)
                ·
                  refine ⟨6080181483317612420545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129710538310775731638293 6080181483317612420545)
                  ·
                    rfl

theorem cell22_53285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_53285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53285 prefixEnd_53285 := by exact prefixLift 53285
  have htrace : WordTrace (prefixWord ++ tailWord_53285) baseStart_53285 baseEnd_53285 := by
    simpa [prefixWord, tailWord_53285, baseEnd_53285] using wordTrace_append hprefix tailTrace_53285
  have hstable : (prefixWord ++ tailWord_53285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53285).length < 2 ^ (prefixWord ++ tailWord_53285).sum := by decide
  have hdescent : baseEnd_53285 < baseStart_53285 := by decide
  rcases family_descends (prefixWord ++ tailWord_53285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53302 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_53302 : Nat := 118140960795 + 53302 * 2 ^ 59
def prefixEnd_53302 : Nat := 4983230072969 + 3 ^ 40 * 53302 * 2
def baseEnd_53302 : Nat := 6082121299123486528861

theorem tailTrace_53302 : CollatzResearch.WordTrace tailWord_53302 prefixEnd_53302 6082121299123486528861 := by
  unfold tailWord_53302
  simp only [CollatzResearch.WordTrace]
  refine ⟨121505228306464506372635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1296055768602288067974773 121505228306464506372635)
  ·
    refine ⟨182257842459696759558953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121505228306464506372635 182257842459696759558953)
    ·
      refine ⟨136693381844772569669215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182257842459696759558953 136693381844772569669215)
      ·
        refine ⟨205040072767158854503823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136693381844772569669215 205040072767158854503823)
        ·
          refine ⟨307560109150738281755735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205040072767158854503823 307560109150738281755735)
          ·
            refine ⟨461340163726107422633603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307560109150738281755735 461340163726107422633603)
            ·
              refine ⟨692010245589161133950405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461340163726107422633603 692010245589161133950405)
              ·
                refine ⟨129751921047967712615701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692010245589161133950405 129751921047967712615701)
                ·
                  refine ⟨6082121299123486528861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129751921047967712615701 6082121299123486528861)
                  ·
                    rfl

theorem cell22_53302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_53302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53302 prefixEnd_53302 := by exact prefixLift 53302
  have htrace : WordTrace (prefixWord ++ tailWord_53302) baseStart_53302 baseEnd_53302 := by
    simpa [prefixWord, tailWord_53302, baseEnd_53302] using wordTrace_append hprefix tailTrace_53302
  have hstable : (prefixWord ++ tailWord_53302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53302).length < 2 ^ (prefixWord ++ tailWord_53302).sum := by decide
  have hdescent : baseEnd_53302 < baseStart_53302 := by decide
  rcases family_descends (prefixWord ++ tailWord_53302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53304 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_53304 : Nat := 118140960795 + 53304 * 2 ^ 59
def prefixEnd_53304 : Nat := 4983230072969 + 3 ^ 40 * 53304 * 2
def baseEnd_53304 : Nat := 18247048538243121036577

theorem tailTrace_53304 : CollatzResearch.WordTrace tailWord_53304 prefixEnd_53304 18247048538243121036577 := by
  unfold tailWord_53304
  simp only [CollatzResearch.WordTrace]
  refine ⟨972078299448093221767483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1296104399264124295689977 972078299448093221767483)
  ·
    refine ⟨1458117449172139832651225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972078299448093221767483 1458117449172139832651225)
    ·
      refine ⟨1093588086879104874488419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458117449172139832651225 1093588086879104874488419)
      ·
        refine ⟨1640382130318657311732629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093588086879104874488419 1640382130318657311732629)
        ·
          refine ⟨76892912358687061487467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1640382130318657311732629 76892912358687061487467)
          ·
            refine ⟨115339368538030592231201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76892912358687061487467 115339368538030592231201)
            ·
              refine ⟨86504526403522944173401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115339368538030592231201 86504526403522944173401)
              ·
                refine ⟨64878394802642208130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86504526403522944173401 64878394802642208130051)
                ·
                  refine ⟨97317592203963312195077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64878394802642208130051 97317592203963312195077)
                  ·
                    refine ⟨18247048538243121036577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97317592203963312195077 18247048538243121036577)
                    ·
                      rfl

theorem cell22_53304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_53304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53304 prefixEnd_53304 := by exact prefixLift 53304
  have htrace : WordTrace (prefixWord ++ tailWord_53304) baseStart_53304 baseEnd_53304 := by
    simpa [prefixWord, tailWord_53304, baseEnd_53304] using wordTrace_append hprefix tailTrace_53304
  have hstable : (prefixWord ++ tailWord_53304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53304).length < 2 ^ (prefixWord ++ tailWord_53304).sum := by decide
  have hdescent : baseEnd_53304 < baseStart_53304 := by decide
  rcases family_descends (prefixWord ++ tailWord_53304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53392 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_53392 : Nat := 118140960795 + 53392 * 2 ^ 59
def prefixEnd_53392 : Nat := 4983230072969 + 3 ^ 40 * 53392 * 2
def baseEnd_53392 : Nat := 6092390912213408278769

theorem tailTrace_53392 : CollatzResearch.WordTrace tailWord_53392 prefixEnd_53392 6092390912213408278769 := by
  unfold tailWord_53392
  simp only [CollatzResearch.WordTrace]
  refine ⟨973683111288688736369215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1298244148384918315158953 973683111288688736369215)
  ·
    refine ⟨1460524666933033104553823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 973683111288688736369215 1460524666933033104553823)
    ·
      refine ⟨2190787000399549656830735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460524666933033104553823 2190787000399549656830735)
      ·
        refine ⟨3286180500599324485246103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190787000399549656830735 3286180500599324485246103)
        ·
          refine ⟨4929270750898986727869155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286180500599324485246103 4929270750898986727869155)
          ·
            refine ⟨7393906126348480091803733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929270750898986727869155 7393906126348480091803733)
            ·
              refine ⟨86647337418146251075825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 7393906126348480091803733 86647337418146251075825)
              ·
                refine ⟨64985503063609688306869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86647337418146251075825 64985503063609688306869)
                ·
                  refine ⟨6092390912213408278769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64985503063609688306869 6092390912213408278769)
                  ·
                    rfl

theorem cell22_53392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_53392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53392 prefixEnd_53392 := by exact prefixLift 53392
  have htrace : WordTrace (prefixWord ++ tailWord_53392) baseStart_53392 baseEnd_53392 := by
    simpa [prefixWord, tailWord_53392, baseEnd_53392] using wordTrace_append hprefix tailTrace_53392
  have hstable : (prefixWord ++ tailWord_53392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53392).length < 2 ^ (prefixWord ++ tailWord_53392).sum := by decide
  have hdescent : baseEnd_53392 < baseStart_53392 := by decide
  rcases family_descends (prefixWord ++ tailWord_53392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53407 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_53407 : Nat := 118140960795 + 53407 * 2 ^ 59
def prefixEnd_53407 : Nat := 4983230072969 + 3 ^ 40 * 53407 * 2
def baseEnd_53407 : Nat := 18282307543185185711261

theorem tailTrace_53407 : CollatzResearch.WordTrace tailWord_53407 prefixEnd_53407 18282307543185185711261 := by
  unfold tailWord_53407
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947913317523035034534475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1298608878348690023022983 1947913317523035034534475)
  ·
    refine ⟨2921869976284552551801713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1947913317523035034534475 2921869976284552551801713)
    ·
      refine ⟨2191402482213414413851285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2921869976284552551801713 2191402482213414413851285)
      ·
        refine ⟨102721991353753800649279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2191402482213414413851285 102721991353753800649279)
        ·
          refine ⟨154082987030630700973919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102721991353753800649279 154082987030630700973919)
          ·
            refine ⟨231124480545946051460879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154082987030630700973919 231124480545946051460879)
            ·
              refine ⟨346686720818919077191319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231124480545946051460879 346686720818919077191319)
              ·
                refine ⟨520030081228378615786979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346686720818919077191319 520030081228378615786979)
                ·
                  refine ⟨780045121842567923680469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520030081228378615786979 780045121842567923680469)
                  ·
                    refine ⟨18282307543185185711261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 780045121842567923680469 18282307543185185711261)
                    ·
                      rfl

theorem cell22_53407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_53407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53407 prefixEnd_53407 := by exact prefixLift 53407
  have htrace : WordTrace (prefixWord ++ tailWord_53407) baseStart_53407 baseEnd_53407 := by
    simpa [prefixWord, tailWord_53407, baseEnd_53407] using wordTrace_append hprefix tailTrace_53407
  have hstable : (prefixWord ++ tailWord_53407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53407).length < 2 ^ (prefixWord ++ tailWord_53407).sum := by decide
  have hdescent : baseEnd_53407 < baseStart_53407 := by decide
  rcases family_descends (prefixWord ++ tailWord_53407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53454 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_53454 : Nat := 118140960795 + 53454 * 2 ^ 59
def prefixEnd_53454 : Nat := 4983230072969 + 3 ^ 40 * 53454 * 2
def baseEnd_53454 : Nat := 6099465534564243262039

theorem tailTrace_53454 : CollatzResearch.WordTrace tailWord_53454 prefixEnd_53454 6099465534564243262039 := by
  unfold tailWord_53454
  simp only [CollatzResearch.WordTrace]
  refine ⟨243703443544095257686927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1299751698901841374330277 243703443544095257686927)
  ·
    refine ⟨365555165316142886530391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243703443544095257686927 365555165316142886530391)
    ·
      refine ⟨548332747974214329795587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365555165316142886530391 548332747974214329795587)
      ·
        refine ⟨822499121961321494693381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548332747974214329795587 822499121961321494693381)
        ·
          refine ⟨154218585367747780255009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 822499121961321494693381 154218585367747780255009)
          ·
            refine ⟨115663939025810835191257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154218585367747780255009 115663939025810835191257)
            ·
              refine ⟨86747954269358126393443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115663939025810835191257 86747954269358126393443)
              ·
                refine ⟨130121931404037189590165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86747954269358126393443 130121931404037189590165)
                ·
                  refine ⟨6099465534564243262039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130121931404037189590165 6099465534564243262039)
                  ·
                    rfl

theorem cell22_53454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_53454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53454 prefixEnd_53454 := by exact prefixLift 53454
  have htrace : WordTrace (prefixWord ++ tailWord_53454) baseStart_53454 baseEnd_53454 := by
    simpa [prefixWord, tailWord_53454, baseEnd_53454] using wordTrace_append hprefix tailTrace_53454
  have hstable : (prefixWord ++ tailWord_53454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53454).length < 2 ^ (prefixWord ++ tailWord_53454).sum := by decide
  have hdescent : baseEnd_53454 < baseStart_53454 := by decide
  rcases family_descends (prefixWord ++ tailWord_53454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53482 : List Nat := [3, 1, 3, 1, 1, 2, 3, 8]
def baseStart_53482 : Nat := 118140960795 + 53482 * 2 ^ 59
def prefixEnd_53482 : Nat := 4983230072969 + 3 ^ 40 * 53482 * 2
def baseEnd_53482 : Nat := 2034220175101110009559

theorem tailTrace_53482 : CollatzResearch.WordTrace tailWord_53482 prefixEnd_53482 2034220175101110009559 := by
  unfold tailWord_53482
  simp only [CollatzResearch.WordTrace]
  refine ⟨487662198062830710878675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1300432528167548562343133 487662198062830710878675)
  ·
    refine ⟨731493297094246066318013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487662198062830710878675 731493297094246066318013)
    ·
      refine ⟨274309986410342274869255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 731493297094246066318013 274309986410342274869255)
      ·
        refine ⟨411464979615513412303883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274309986410342274869255 411464979615513412303883)
        ·
          refine ⟨617197469423270118455825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411464979615513412303883 617197469423270118455825)
          ·
            refine ⟨462898102067452588841869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617197469423270118455825 462898102067452588841869)
            ·
              refine ⟨173586788275294720815701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462898102067452588841869 173586788275294720815701)
              ·
                refine ⟨2034220175101110009559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 173586788275294720815701 2034220175101110009559)
                ·
                  rfl

theorem cell22_53482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_53482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53482 prefixEnd_53482 := by exact prefixLift 53482
  have htrace : WordTrace (prefixWord ++ tailWord_53482) baseStart_53482 baseEnd_53482 := by
    simpa [prefixWord, tailWord_53482, baseEnd_53482] using wordTrace_append hprefix tailTrace_53482
  have hstable : (prefixWord ++ tailWord_53482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53482).length < 2 ^ (prefixWord ++ tailWord_53482).sum := by decide
  have hdescent : baseEnd_53482 < baseStart_53482 := by decide
  rcases family_descends (prefixWord ++ tailWord_53482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53561 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 5]
def baseStart_53561 : Nat := 118140960795 + 53561 * 2 ^ 59
def prefixEnd_53561 : Nat := 4983230072969 + 3 ^ 40 * 53561 * 2
def baseEnd_53561 : Nat := 6111674963460039120263

theorem tailTrace_53561 : CollatzResearch.WordTrace tailWord_53561 prefixEnd_53561 6111674963460039120263 := by
  unfold tailWord_53561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953530158965119335640537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1302353439310079557093691 1953530158965119335640537)
  ·
    refine ⟨1465147619223839501730403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1953530158965119335640537 1465147619223839501730403)
    ·
      refine ⟨2197721428835759252595605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465147619223839501730403 2197721428835759252595605)
      ·
        refine ⟨103018191976676214965419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2197721428835759252595605 103018191976676214965419)
        ·
          refine ⟨154527287965014322448129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103018191976676214965419 154527287965014322448129)
          ·
            refine ⟨115895465973760741836097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154527287965014322448129 115895465973760741836097)
            ·
              refine ⟨86921599480320556377073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115895465973760741836097 86921599480320556377073)
              ·
                refine ⟨65191199610240417282805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86921599480320556377073 65191199610240417282805)
                ·
                  refine ⟨6111674963460039120263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65191199610240417282805 6111674963460039120263)
                  ·
                    rfl

theorem cell22_53561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_53561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53561 prefixEnd_53561 := by exact prefixLift 53561
  have htrace : WordTrace (prefixWord ++ tailWord_53561) baseStart_53561 baseEnd_53561 := by
    simpa [prefixWord, tailWord_53561, baseEnd_53561] using wordTrace_append hprefix tailTrace_53561
  have hstable : (prefixWord ++ tailWord_53561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53561).length < 2 ^ (prefixWord ++ tailWord_53561).sum := by decide
  have hdescent : baseEnd_53561 < baseStart_53561 := by decide
  rcases family_descends (prefixWord ++ tailWord_53561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53604 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_53604 : Nat := 118140960795 + 53604 * 2 ^ 59
def prefixEnd_53604 : Nat := 4983230072969 + 3 ^ 40 * 53604 * 2
def baseEnd_53604 : Nat := 18349744669142338535657

theorem tailTrace_53604 : CollatzResearch.WordTrace tailWord_53604 prefixEnd_53604 18349744669142338535657 := by
  unfold tailWord_53604
  simp only [CollatzResearch.WordTrace]
  refine ⟨977549248904668839727933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1303398998539558452970577 977549248904668839727933)
  ·
    refine ⟨366580968339250814897975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 977549248904668839727933 366580968339250814897975)
    ·
      refine ⟨549871452508876222346963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366580968339250814897975 549871452508876222346963)
      ·
        refine ⟨824807178763314333520445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549871452508876222346963 824807178763314333520445)
        ·
          refine ⟨309302692036242875070167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 824807178763314333520445 309302692036242875070167)
          ·
            refine ⟨463954038054364312605251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309302692036242875070167 463954038054364312605251)
            ·
              refine ⟨695931057081546468907877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463954038054364312605251 695931057081546468907877)
              ·
                refine ⟨130487073202789962920227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695931057081546468907877 130487073202789962920227)
                ·
                  refine ⟨195730609804184944380341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130487073202789962920227 195730609804184944380341)
                  ·
                    refine ⟨18349744669142338535657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195730609804184944380341 18349744669142338535657)
                    ·
                      rfl

theorem cell22_53604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_53604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53604 prefixEnd_53604 := by exact prefixLift 53604
  have htrace : WordTrace (prefixWord ++ tailWord_53604) baseStart_53604 baseEnd_53604 := by
    simpa [prefixWord, tailWord_53604, baseEnd_53604] using wordTrace_append hprefix tailTrace_53604
  have hstable : (prefixWord ++ tailWord_53604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53604).length < 2 ^ (prefixWord ++ tailWord_53604).sum := by decide
  have hdescent : baseEnd_53604 < baseStart_53604 := by decide
  rcases family_descends (prefixWord ++ tailWord_53604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53608 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_53608 : Nat := 118140960795 + 53608 * 2 ^ 59
def prefixEnd_53608 : Nat := 4983230072969 + 3 ^ 40 * 53608 * 2
def baseEnd_53608 : Nat := 18351113950887661435645

theorem tailTrace_53608 : CollatzResearch.WordTrace tailWord_53608 prefixEnd_53608 18351113950887661435645 := by
  unfold tailWord_53608
  simp only [CollatzResearch.WordTrace]
  refine ⟨977622194897423181300739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1303496259863230908400985 977622194897423181300739)
  ·
    refine ⟨1466433292346134771951109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977622194897423181300739 1466433292346134771951109)
    ·
      refine ⟨274956242314900269740833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1466433292346134771951109 274956242314900269740833)
      ·
        refine ⟨206217181736175202305625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274956242314900269740833 206217181736175202305625)
        ·
          refine ⟨154662886302131401729219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206217181736175202305625 154662886302131401729219)
          ·
            refine ⟨231994329453197102593829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154662886302131401729219 231994329453197102593829)
            ·
              refine ⟨43498936772474456736343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231994329453197102593829 43498936772474456736343)
              ·
                refine ⟨65248405158711685104515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43498936772474456736343 65248405158711685104515)
                ·
                  refine ⟨97872607738067527656773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65248405158711685104515 97872607738067527656773)
                  ·
                    refine ⟨18351113950887661435645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97872607738067527656773 18351113950887661435645)
                    ·
                      rfl

theorem cell22_53608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_53608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53608 prefixEnd_53608 := by exact prefixLift 53608
  have htrace : WordTrace (prefixWord ++ tailWord_53608) baseStart_53608 baseEnd_53608 := by
    simpa [prefixWord, tailWord_53608, baseEnd_53608] using wordTrace_append hprefix tailTrace_53608
  have hstable : (prefixWord ++ tailWord_53608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53608).length < 2 ^ (prefixWord ++ tailWord_53608).sum := by decide
  have hdescent : baseEnd_53608 < baseStart_53608 := by decide
  rcases family_descends (prefixWord ++ tailWord_53608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53674 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_53674 : Nat := 118140960795 + 53674 * 2 ^ 59
def prefixEnd_53674 : Nat := 4983230072969 + 3 ^ 40 * 53674 * 2
def baseEnd_53674 : Nat := 6124569033228496428481

theorem tailTrace_53674 : CollatzResearch.WordTrace tailWord_53674 prefixEnd_53674 6124569033228496428481 := by
  unfold tailWord_53674
  simp only [CollatzResearch.WordTrace]
  refine ⟨489412901888934908626019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1305101071703826423002717 489412901888934908626019)
  ·
    refine ⟨734119352833402362939029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 489412901888934908626019 734119352833402362939029)
    ·
      refine ⟨34411844664065735762767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 734119352833402362939029 34411844664065735762767)
      ·
        refine ⟨51617766996098603644151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34411844664065735762767 51617766996098603644151)
        ·
          refine ⟨77426650494147905466227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51617766996098603644151 77426650494147905466227)
          ·
            refine ⟨116139975741221858199341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77426650494147905466227 116139975741221858199341)
            ·
              refine ⟨43552490902958196824753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116139975741221858199341 43552490902958196824753)
              ·
                refine ⟨32664368177218647618565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43552490902958196824753 32664368177218647618565)
                ·
                  refine ⟨6124569033228496428481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32664368177218647618565 6124569033228496428481)
                  ·
                    rfl

theorem cell22_53674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_53674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_53674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_53674 prefixEnd_53674 := by exact prefixLift 53674
  have htrace : WordTrace (prefixWord ++ tailWord_53674) baseStart_53674 baseEnd_53674 := by
    simpa [prefixWord, tailWord_53674, baseEnd_53674] using wordTrace_append hprefix tailTrace_53674
  have hstable : (prefixWord ++ tailWord_53674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53674).length < 2 ^ (prefixWord ++ tailWord_53674).sum := by decide
  have hdescent : baseEnd_53674 < baseStart_53674 := by decide
  rcases family_descends (prefixWord ++ tailWord_53674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
