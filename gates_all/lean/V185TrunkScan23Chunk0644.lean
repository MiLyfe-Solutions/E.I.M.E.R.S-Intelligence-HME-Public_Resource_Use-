import V185TrunkScan23Chunk0643

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3808026 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_3808026 : Nat := 118140960795 + 3808026 * 2 ^ 59
def prefixEnd_3808026 : Nat := 4983230072969 + 3 ^ 40 * 3808026 * 2
def baseEnd_3808026 : Nat := 1955347682818223314462213

theorem tailTrace_3808026 : CollatzResearch.WordTrace tailWord_3808026 prefixEnd_3808026 1955347682818223314462213 := by
  unfold tailWord_3808026
  simp only [CollatzResearch.WordTrace]
  refine ⟨34722529625544908977044983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92593412334786423938786621 34722529625544908977044983)
  ·
    refine ⟨52083794438317363465567475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34722529625544908977044983 52083794438317363465567475)
    ·
      refine ⟨78125691657476045198351213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52083794438317363465567475 78125691657476045198351213)
      ·
        refine ⟨29297134371553516949381705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78125691657476045198351213 29297134371553516949381705)
        ·
          refine ⟨21972850778665137712036279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29297134371553516949381705 21972850778665137712036279)
          ·
            refine ⟨32959276167997706568054419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972850778665137712036279 32959276167997706568054419)
            ·
              refine ⟨49438914251996559852081629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32959276167997706568054419 49438914251996559852081629)
              ·
                refine ⟨18539592844498709944530611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49438914251996559852081629 18539592844498709944530611)
                ·
                  refine ⟨27809389266748064916795917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18539592844498709944530611 27809389266748064916795917)
                  ·
                    refine ⟨10428520975030524343798469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27809389266748064916795917 10428520975030524343798469)
                    ·
                      refine ⟨1955347682818223314462213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10428520975030524343798469 1955347682818223314462213)
                      ·
                        rfl

theorem cell23_3808026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_3808026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808026 prefixEnd_3808026 := by exact prefixLift 3808026
  have htrace : WordTrace (prefixWord ++ tailWord_3808026) baseStart_3808026 baseEnd_3808026 := by
    simpa [prefixWord, tailWord_3808026, baseEnd_3808026] using wordTrace_append hprefix tailTrace_3808026
  have hstable : (prefixWord ++ tailWord_3808026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808026).length < 2 ^ (prefixWord ++ tailWord_3808026).sum := by decide
  have hdescent : baseEnd_3808026 < baseStart_3808026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808077 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3808077 : Nat := 118140960795 + 3808077 * 2 ^ 59
def prefixEnd_3808077 : Nat := 4983230072969 + 3 ^ 40 * 3808077 * 2
def baseEnd_3808077 : Nat := 1955373870331602614924479

theorem tailTrace_3808077 : CollatzResearch.WordTrace tailWord_3808077 prefixEnd_3808077 1955373870331602614924479 := by
  unfold tailWord_3808077
  simp only [CollatzResearch.WordTrace]
  refine ⟨138891978624994871618286485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92594652416663247745524323 138891978624994871618286485)
  ·
    refine ⟨6510561498046634607107179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138891978624994871618286485 6510561498046634607107179)
    ·
      refine ⟨9765842247069951910660769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510561498046634607107179 9765842247069951910660769)
      ·
        refine ⟨7324381685302463932995577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9765842247069951910660769 7324381685302463932995577)
        ·
          refine ⟨5493286263976847949746683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7324381685302463932995577 5493286263976847949746683)
          ·
            refine ⟨8239929395965271924620025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493286263976847949746683 8239929395965271924620025)
            ·
              refine ⟨6179947046973953943465019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8239929395965271924620025 6179947046973953943465019)
              ·
                refine ⟨9269920570460930915197529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179947046973953943465019 9269920570460930915197529)
                ·
                  refine ⟨6952440427845698186398147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269920570460930915197529 6952440427845698186398147)
                  ·
                    refine ⟨10428660641768547279597221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952440427845698186398147 10428660641768547279597221)
                    ·
                      refine ⟨1955373870331602614924479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10428660641768547279597221 1955373870331602614924479)
                      ·
                        rfl

theorem cell23_3808077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3808077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808077 prefixEnd_3808077 := by exact prefixLift 3808077
  have htrace : WordTrace (prefixWord ++ tailWord_3808077) baseStart_3808077 baseEnd_3808077 := by
    simpa [prefixWord, tailWord_3808077, baseEnd_3808077] using wordTrace_append hprefix tailTrace_3808077
  have hstable : (prefixWord ++ tailWord_3808077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808077).length < 2 ^ (prefixWord ++ tailWord_3808077).sum := by decide
  have hdescent : baseEnd_3808077 < baseStart_3808077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808104 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 1, 4]
def baseStart_3808104 : Nat := 118140960795 + 3808104 * 2 ^ 59
def prefixEnd_3808104 : Nat := 4983230072969 + 3 ^ 40 * 3808104 * 2
def baseEnd_3808104 : Nat := 651795911436424669762285

theorem tailTrace_3808104 : CollatzResearch.WordTrace tailWord_3808104 prefixEnd_3808104 651795911436424669762285 := by
  unfold tailWord_3808104
  simp only [CollatzResearch.WordTrace]
  refine ⟨69446481697948527614759683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92595308930598036819679577 69446481697948527614759683)
  ·
    refine ⟨104169722546922791422139525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69446481697948527614759683 104169722546922791422139525)
    ·
      refine ⟨19531822977548023391651161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104169722546922791422139525 19531822977548023391651161)
      ·
        refine ⟨14648867233161017543738371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19531822977548023391651161 14648867233161017543738371)
        ·
          refine ⟨21973300849741526315607557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648867233161017543738371 21973300849741526315607557)
          ·
            refine ⟨4119993909326536184176417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21973300849741526315607557 4119993909326536184176417)
            ·
              refine ⟨3089995431994902138132313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119993909326536184176417 3089995431994902138132313)
              ·
                refine ⟨2317496573996176603599235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089995431994902138132313 2317496573996176603599235)
                ·
                  refine ⟨3476244860994264905398853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317496573996176603599235 3476244860994264905398853)
                  ·
                    refine ⟨651795911436424669762285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476244860994264905398853 651795911436424669762285)
                    ·
                      rfl

theorem cell23_3808104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_3808104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808104 prefixEnd_3808104 := by exact prefixLift 3808104
  have htrace : WordTrace (prefixWord ++ tailWord_3808104) baseStart_3808104 baseEnd_3808104 := by
    simpa [prefixWord, tailWord_3808104, baseEnd_3808104] using wordTrace_append hprefix tailTrace_3808104
  have hstable : (prefixWord ++ tailWord_3808104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808104).length < 2 ^ (prefixWord ++ tailWord_3808104).sum := by decide
  have hdescent : baseEnd_3808104 < baseStart_3808104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808133 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3808133 : Nat := 118140960795 + 3808133 * 2 ^ 59
def prefixEnd_3808133 : Nat := 4983230072969 + 3 ^ 40 * 3808133 * 2
def baseEnd_3808133 : Nat := 1955402625248254395824221

theorem tailTrace_3808133 : CollatzResearch.WordTrace tailWord_3808133 prefixEnd_3808133 1955402625248254395824221 := by
  unfold tailWord_3808133
  simp only [CollatzResearch.WordTrace]
  refine ⟨138894021112791993182325053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92596014075194662121550035 138894021112791993182325053)
  ·
    refine ⟨52085257917296997443371895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138894021112791993182325053 52085257917296997443371895)
    ·
      refine ⟨78127886875945496165057843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52085257917296997443371895 78127886875945496165057843)
      ·
        refine ⟨117191830313918244247586765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78127886875945496165057843 117191830313918244247586765)
        ·
          refine ⟨43946936367719341592845037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117191830313918244247586765 43946936367719341592845037)
          ·
            refine ⟨16480101137894753097316889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43946936367719341592845037 16480101137894753097316889)
            ·
              refine ⟨12360075853421064822987667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16480101137894753097316889 12360075853421064822987667)
              ·
                refine ⟨18540113780131597234481501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12360075853421064822987667 18540113780131597234481501)
                ·
                  refine ⟨6952542667549348962930563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18540113780131597234481501 6952542667549348962930563)
                  ·
                    refine ⟨10428814001324023444395845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952542667549348962930563 10428814001324023444395845)
                    ·
                      refine ⟨1955402625248254395824221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10428814001324023444395845 1955402625248254395824221)
                      ·
                        rfl

theorem cell23_3808133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3808133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808133 prefixEnd_3808133 := by exact prefixLift 3808133
  have htrace : WordTrace (prefixWord ++ tailWord_3808133) baseStart_3808133 baseEnd_3808133 := by
    simpa [prefixWord, tailWord_3808133, baseEnd_3808133] using wordTrace_append hprefix tailTrace_3808133
  have hstable : (prefixWord ++ tailWord_3808133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808133).length < 2 ^ (prefixWord ++ tailWord_3808133).sum := by decide
  have hdescent : baseEnd_3808133 < baseStart_3808133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808137 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 2, 3, 2]
def baseStart_3808137 : Nat := 118140960795 + 3808137 * 2 ^ 59
def prefixEnd_3808137 : Nat := 4983230072969 + 3 ^ 40 * 3808137 * 2
def baseEnd_3808137 : Nat := 1955404679170872380174203

theorem tailTrace_3808137 : CollatzResearch.WordTrace tailWord_3808137 prefixEnd_3808137 1955404679170872380174203 := by
  unfold tailWord_3808137
  simp only [CollatzResearch.WordTrace]
  refine ⟨138894167004777501865470665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92596111336518334576980443 138894167004777501865470665)
  ·
    refine ⟨104170625253583126399102999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138894167004777501865470665 104170625253583126399102999)
    ·
      refine ⟨156255937880374689598654499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104170625253583126399102999 156255937880374689598654499)
      ·
        refine ⟨234383906820562034397981749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156255937880374689598654499 234383906820562034397981749)
        ·
          refine ⟨21973491264427690724810789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234383906820562034397981749 21973491264427690724810789)
          ·
            refine ⟨4120029612080192010902023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21973491264427690724810789 4120029612080192010902023)
            ·
              refine ⟨6180044418120288016353035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120029612080192010902023 6180044418120288016353035)
              ·
                refine ⟨9270066627180432024529553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180044418120288016353035 9270066627180432024529553)
                ·
                  refine ⟨6952549970385324018397165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270066627180432024529553 6952549970385324018397165)
                  ·
                    refine ⟨2607206238894496506898937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6952549970385324018397165 2607206238894496506898937)
                    ·
                      refine ⟨1955404679170872380174203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607206238894496506898937 1955404679170872380174203)
                      ·
                        rfl

theorem cell23_3808137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3, 2].length) (baseStart_3808137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808137 prefixEnd_3808137 := by exact prefixLift 3808137
  have htrace : WordTrace (prefixWord ++ tailWord_3808137) baseStart_3808137 baseEnd_3808137 := by
    simpa [prefixWord, tailWord_3808137, baseEnd_3808137] using wordTrace_append hprefix tailTrace_3808137
  have hstable : (prefixWord ++ tailWord_3808137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808137).length < 2 ^ (prefixWord ++ tailWord_3808137).sum := by decide
  have hdescent : baseEnd_3808137 < baseStart_3808137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808160 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_3808160 : Nat := 118140960795 + 3808160 * 2 ^ 59
def prefixEnd_3808160 : Nat := 4983230072969 + 3 ^ 40 * 3808160 * 2
def baseEnd_3808160 : Nat := 651805496408641930062199

theorem tailTrace_3808160 : CollatzResearch.WordTrace tailWord_3808160 prefixEnd_3808160 651805496408641930062199 := by
  unfold tailWord_3808160
  simp only [CollatzResearch.WordTrace]
  refine ⟨69447502941847088396778967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92596670589129451195705289 69447502941847088396778967)
  ·
    refine ⟨104171254412770632595168451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69447502941847088396778967 104171254412770632595168451)
    ·
      refine ⟨156256881619155948892752677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104171254412770632595168451 156256881619155948892752677)
      ·
        refine ⟨29298165303591740417391127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156256881619155948892752677 29298165303591740417391127)
        ·
          refine ⟨43947247955387610626086691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29298165303591740417391127 43947247955387610626086691)
          ·
            refine ⟨65920871933081415939130037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43947247955387610626086691 65920871933081415939130037)
            ·
              refine ⟨6180081743726382744293441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65920871933081415939130037 6180081743726382744293441)
              ·
                refine ⟨4635061307794787058220081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180081743726382744293441 4635061307794787058220081)
                ·
                  refine ⟨3476295980846090293665061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635061307794787058220081 3476295980846090293665061)
                  ·
                    refine ⟨651805496408641930062199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476295980846090293665061 651805496408641930062199)
                    ·
                      rfl

theorem cell23_3808160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_3808160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808160 prefixEnd_3808160 := by exact prefixLift 3808160
  have htrace : WordTrace (prefixWord ++ tailWord_3808160) baseStart_3808160 baseEnd_3808160 := by
    simpa [prefixWord, tailWord_3808160, baseEnd_3808160] using wordTrace_append hprefix tailTrace_3808160
  have hstable : (prefixWord ++ tailWord_3808160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808160).length < 2 ^ (prefixWord ++ tailWord_3808160).sum := by decide
  have hdescent : baseEnd_3808160 < baseStart_3808160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808177 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_3808177 : Nat := 118140960795 + 3808177 * 2 ^ 59
def prefixEnd_3808177 : Nat := 4983230072969 + 3 ^ 40 * 3808177 * 2
def baseEnd_3808177 : Nat := 651808406132350741224673

theorem tailTrace_3808177 : CollatzResearch.WordTrace tailWord_3808177 prefixEnd_3808177 651808406132350741224673 := by
  unfold tailWord_3808177
  simp only [CollatzResearch.WordTrace]
  refine ⟨138895625924632588696926785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92597083949755059131284523 138895625924632588696926785)
  ·
    refine ⟨104171719443474441522695089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138895625924632588696926785 104171719443474441522695089)
    ·
      refine ⟨78128789582605831142021317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104171719443474441522695089 78128789582605831142021317)
      ·
        refine ⟨14649148046738593339128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78128789582605831142021317 14649148046738593339128997)
        ·
          refine ⟨2746715258763486251086687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14649148046738593339128997 2746715258763486251086687)
          ·
            refine ⟨4120072888145229376630031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746715258763486251086687 4120072888145229376630031)
            ·
              refine ⟨6180109332217844064945047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120072888145229376630031 6180109332217844064945047)
              ·
                refine ⟨9270163998326766097417571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180109332217844064945047 9270163998326766097417571)
                ·
                  refine ⟨13905245997490149146126357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270163998326766097417571 13905245997490149146126357)
                  ·
                    refine ⟨651808406132350741224673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13905245997490149146126357 651808406132350741224673)
                    ·
                      rfl

theorem cell23_3808177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_3808177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808177 prefixEnd_3808177 := by exact prefixLift 3808177
  have htrace : WordTrace (prefixWord ++ tailWord_3808177) baseStart_3808177 baseEnd_3808177 := by
    simpa [prefixWord, tailWord_3808177, baseEnd_3808177] using wordTrace_append hprefix tailTrace_3808177
  have hstable : (prefixWord ++ tailWord_3808177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808177).length < 2 ^ (prefixWord ++ tailWord_3808177).sum := by decide
  have hdescent : baseEnd_3808177 < baseStart_3808177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808234 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_3808234 : Nat := 118140960795 + 3808234 * 2 ^ 59
def prefixEnd_3808234 : Nat := 4983230072969 + 3 ^ 40 * 3808234 * 2
def baseEnd_3808234 : Nat := 1955454486794358500661257

theorem tailTrace_3808234 : CollatzResearch.WordTrace tailWord_3808234 prefixEnd_3808234 1955454486794358500661257 := by
  unfold tailWord_3808234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724426221356521857937939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92598469923617391621167837 34724426221356521857937939)
  ·
    refine ⟨52086639332034782786906909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724426221356521857937939 52086639332034782786906909)
    ·
      refine ⟨19532489749513043545090091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52086639332034782786906909 19532489749513043545090091)
      ·
        refine ⟨29298734624269565317635137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532489749513043545090091 29298734624269565317635137)
        ·
          refine ⟨21974050968202173988226353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298734624269565317635137 21974050968202173988226353)
          ·
            refine ⟨16480538226151630491169765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21974050968202173988226353 16480538226151630491169765)
            ·
              refine ⟨3090100917403430717094331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16480538226151630491169765 3090100917403430717094331)
              ·
                refine ⟨4635151376105146075641497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090100917403430717094331 4635151376105146075641497)
                ·
                  refine ⟨3476363532078859556731123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635151376105146075641497 3476363532078859556731123)
                  ·
                    refine ⟨5214545298118289335096685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476363532078859556731123 5214545298118289335096685)
                    ·
                      refine ⟨1955454486794358500661257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214545298118289335096685 1955454486794358500661257)
                      ·
                        rfl

theorem cell23_3808234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_3808234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808234 prefixEnd_3808234 := by exact prefixLift 3808234
  have htrace : WordTrace (prefixWord ++ tailWord_3808234) baseStart_3808234 baseEnd_3808234 := by
    simpa [prefixWord, tailWord_3808234, baseEnd_3808234] using wordTrace_append hprefix tailTrace_3808234
  have hstable : (prefixWord ++ tailWord_3808234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808234).length < 2 ^ (prefixWord ++ tailWord_3808234).sum := by decide
  have hdescent : baseEnd_3808234 < baseStart_3808234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808240 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2]
def baseStart_3808240 : Nat := 118140960795 + 3808240 * 2 ^ 59
def prefixEnd_3808240 : Nat := 4983230072969 + 3 ^ 40 * 3808240 * 2
def baseEnd_3808240 : Nat := 1955457567678285477186229

theorem tailTrace_3808240 : CollatzResearch.WordTrace tailWord_3808240 prefixEnd_3808240 1955457567678285477186229 := by
  unfold tailWord_3808240
  simp only [CollatzResearch.WordTrace]
  refine ⟨69448961861702175228235087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92598615815602900304313449 69448961861702175228235087)
  ·
    refine ⟨104173442792553262842352631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69448961861702175228235087 104173442792553262842352631)
    ·
      refine ⟨156260164188829894263528947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104173442792553262842352631 156260164188829894263528947)
      ·
        refine ⟨234390246283244841395293421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156260164188829894263528947 234390246283244841395293421)
        ·
          refine ⟨87896342356216815523235033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234390246283244841395293421 87896342356216815523235033)
          ·
            refine ⟨65922256767162611642426275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87896342356216815523235033 65922256767162611642426275)
            ·
              refine ⟨98883385150743917463639413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65922256767162611642426275 98883385150743917463639413)
              ·
                refine ⟨9270317357882242262216195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98883385150743917463639413 9270317357882242262216195)
                ·
                  refine ⟨13905476036823363393324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270317357882242262216195 13905476036823363393324293)
                  ·
                    refine ⟨2607276756904380636248305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13905476036823363393324293 2607276756904380636248305)
                    ·
                      refine ⟨1955457567678285477186229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607276756904380636248305 1955457567678285477186229)
                      ·
                        rfl

theorem cell23_3808240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 1, 4, 2].length) (baseStart_3808240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808240 prefixEnd_3808240 := by exact prefixLift 3808240
  have htrace : WordTrace (prefixWord ++ tailWord_3808240) baseStart_3808240 baseEnd_3808240 := by
    simpa [prefixWord, tailWord_3808240, baseEnd_3808240] using wordTrace_append hprefix tailTrace_3808240
  have hstable : (prefixWord ++ tailWord_3808240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808240).length < 2 ^ (prefixWord ++ tailWord_3808240).sum := by decide
  have hdescent : baseEnd_3808240 < baseStart_3808240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808253 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3808253 : Nat := 118140960795 + 3808253 * 2 ^ 59
def prefixEnd_3808253 : Nat := 4983230072969 + 3 ^ 40 * 3808253 * 2
def baseEnd_3808253 : Nat := 1955464242926793926323669

theorem tailTrace_3808253 : CollatzResearch.WordTrace tailWord_3808253 prefixEnd_3808253 1955464242926793926323669 := by
  unfold tailWord_3808253
  simp only [CollatzResearch.WordTrace]
  refine ⟨138898397872357253676693413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92598931914904835784462275 138898397872357253676693413)
  ·
    refine ⟨26043449601066985064380015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138898397872357253676693413 26043449601066985064380015)
    ·
      refine ⟨39065174401600477596570023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26043449601066985064380015 39065174401600477596570023)
      ·
        refine ⟨58597761602400716394855035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39065174401600477596570023 58597761602400716394855035)
        ·
          refine ⟨87896642403601074592282553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58597761602400716394855035 87896642403601074592282553)
          ·
            refine ⟨65922481802700805944211915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87896642403601074592282553 65922481802700805944211915)
            ·
              refine ⟨98883722704051208916317873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65922481802700805944211915 98883722704051208916317873)
              ·
                refine ⟨74162792028038406687238405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98883722704051208916317873 74162792028038406687238405)
                ·
                  refine ⟨13905523505257201253857201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74162792028038406687238405 13905523505257201253857201)
                  ·
                    refine ⟨10429142628942900940392901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13905523505257201253857201 10429142628942900940392901)
                    ·
                      refine ⟨1955464242926793926323669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10429142628942900940392901 1955464242926793926323669)
                      ·
                        rfl

theorem cell23_3808253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3808253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808253 prefixEnd_3808253 := by exact prefixLift 3808253
  have htrace : WordTrace (prefixWord ++ tailWord_3808253) baseStart_3808253 baseEnd_3808253 := by
    simpa [prefixWord, tailWord_3808253, baseEnd_3808253] using wordTrace_append hprefix tailTrace_3808253
  have hstable : (prefixWord ++ tailWord_3808253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808253).length < 2 ^ (prefixWord ++ tailWord_3808253).sum := by decide
  have hdescent : baseEnd_3808253 < baseStart_3808253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808257 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_3808257 : Nat := 118140960795 + 3808257 * 2 ^ 59
def prefixEnd_3808257 : Nat := 4983230072969 + 3 ^ 40 * 3808257 * 2
def baseEnd_3808257 : Nat := 1955466296849411910673651

theorem tailTrace_3808257 : CollatzResearch.WordTrace tailWord_3808257 prefixEnd_3808257 1955466296849411910673651 := by
  unfold tailWord_3808257
  simp only [CollatzResearch.WordTrace]
  refine ⟨138898543764342762359839025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92599029176228508239892683 138898543764342762359839025)
  ·
    refine ⟨104173907823257071769879269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138898543764342762359839025 104173907823257071769879269)
    ·
      refine ⟨19532607716860700956852363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104173907823257071769879269 19532607716860700956852363)
      ·
        refine ⟨29298911575291051435278545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532607716860700956852363 29298911575291051435278545)
        ·
          refine ⟨21974183681468288576458909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298911575291051435278545 21974183681468288576458909)
          ·
            refine ⟨8240318880550608216172091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21974183681468288576458909 8240318880550608216172091)
            ·
              refine ⟨12360478320825912324258137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240318880550608216172091 12360478320825912324258137)
              ·
                refine ⟨9270358740619434243193603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360478320825912324258137 9270358740619434243193603)
                ·
                  refine ⟨13905538110929151364790405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270358740619434243193603 13905538110929151364790405)
                  ·
                    refine ⟨2607288395799215880898201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13905538110929151364790405 2607288395799215880898201)
                    ·
                      refine ⟨1955466296849411910673651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607288395799215880898201 1955466296849411910673651)
                      ·
                        rfl

theorem cell23_3808257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_3808257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808257 prefixEnd_3808257 := by exact prefixLift 3808257
  have htrace : WordTrace (prefixWord ++ tailWord_3808257) baseStart_3808257 baseEnd_3808257 := by
    simpa [prefixWord, tailWord_3808257, baseEnd_3808257] using wordTrace_append hprefix tailTrace_3808257
  have hstable : (prefixWord ++ tailWord_3808257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808257).length < 2 ^ (prefixWord ++ tailWord_3808257).sum := by decide
  have hdescent : baseEnd_3808257 < baseStart_3808257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808273 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_3808273 : Nat := 118140960795 + 3808273 * 2 ^ 59
def prefixEnd_3808273 : Nat := 4983230072969 + 3 ^ 40 * 3808273 * 2
def baseEnd_3808273 : Nat := 1955474512539883848073577

theorem tailTrace_3808273 : CollatzResearch.WordTrace tailWord_3808273 prefixEnd_3808273 1955474512539883848073577 := by
  unfold tailWord_3808273
  simp only [CollatzResearch.WordTrace]
  refine ⟨138899127332284797092421473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92599418221523198061614315 138899127332284797092421473)
  ·
    refine ⟨104174345499213597819316105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138899127332284797092421473 104174345499213597819316105)
    ·
      refine ⟨78130759124410198364487079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104174345499213597819316105 78130759124410198364487079)
      ·
        refine ⟨117196138686615297546730619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78130759124410198364487079 117196138686615297546730619)
        ·
          refine ⟨175794208029922946320095929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117196138686615297546730619 175794208029922946320095929)
          ·
            refine ⟨131845656022442209740071947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175794208029922946320095929 131845656022442209740071947)
            ·
              refine ⟨197768484033663314610107921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131845656022442209740071947 197768484033663314610107921)
              ·
                refine ⟨148326363025247485957580941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197768484033663314610107921 148326363025247485957580941)
                ·
                  refine ⟨55622386134467807234092853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148326363025247485957580941 55622386134467807234092853)
                  ·
                    refine ⟨5214598700106356928196205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55622386134467807234092853 5214598700106356928196205)
                    ·
                      refine ⟨1955474512539883848073577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214598700106356928196205 1955474512539883848073577)
                      ·
                        rfl

theorem cell23_3808273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_3808273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808273 prefixEnd_3808273 := by exact prefixLift 3808273
  have htrace : WordTrace (prefixWord ++ tailWord_3808273) baseStart_3808273 baseEnd_3808273 := by
    simpa [prefixWord, tailWord_3808273, baseEnd_3808273] using wordTrace_append hprefix tailTrace_3808273
  have hstable : (prefixWord ++ tailWord_3808273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808273).length < 2 ^ (prefixWord ++ tailWord_3808273).sum := by decide
  have hdescent : baseEnd_3808273 < baseStart_3808273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808290 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3808290 : Nat := 118140960795 + 3808290 * 2 ^ 59
def prefixEnd_3808290 : Nat := 4983230072969 + 3 ^ 40 * 3808290 * 2
def baseEnd_3808290 : Nat := 1955483241711010281560999

theorem tailTrace_3808290 : CollatzResearch.WordTrace tailWord_3808290 prefixEnd_3808290 1955483241711010281560999 := by
  unfold tailWord_3808290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724936843305802248947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92599831582148805997193549 34724936843305802248947581)
  ·
    refine ⟨13021851316239675843355343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34724936843305802248947581 13021851316239675843355343)
    ·
      refine ⟨19532776974359513765033015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021851316239675843355343 19532776974359513765033015)
      ·
        refine ⟨29299165461539270647549523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532776974359513765033015 29299165461539270647549523)
        ·
          refine ⟨43948748192308905971324285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29299165461539270647549523 43948748192308905971324285)
          ·
            refine ⟨16480780572115839739246607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43948748192308905971324285 16480780572115839739246607)
            ·
              refine ⟨24721170858173759608869911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16480780572115839739246607 24721170858173759608869911)
              ·
                refine ⟨37081756287260639413304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24721170858173759608869911 37081756287260639413304867)
                ·
                  refine ⟨55622634430890959119957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37081756287260639413304867 55622634430890959119957301)
                  ·
                    refine ⟨5214621977896027417495997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55622634430890959119957301 5214621977896027417495997)
                    ·
                      refine ⟨1955483241711010281560999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214621977896027417495997 1955483241711010281560999)
                      ·
                        rfl

theorem cell23_3808290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3808290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808290 prefixEnd_3808290 := by exact prefixLift 3808290
  have htrace : WordTrace (prefixWord ++ tailWord_3808290) baseStart_3808290 baseEnd_3808290 := by
    simpa [prefixWord, tailWord_3808290, baseEnd_3808290] using wordTrace_append hprefix tailTrace_3808290
  have hstable : (prefixWord ++ tailWord_3808290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808290).length < 2 ^ (prefixWord ++ tailWord_3808290).sum := by decide
  have hdescent : baseEnd_3808290 < baseStart_3808290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808293 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3808293 : Nat := 118140960795 + 3808293 * 2 ^ 59
def prefixEnd_3808293 : Nat := 4983230072969 + 3 ^ 40 * 3808293 * 2
def baseEnd_3808293 : Nat := 651828260717657923274495

theorem tailTrace_3808293 : CollatzResearch.WordTrace tailWord_3808293 prefixEnd_3808293 651828260717657923274495 := by
  unfold tailWord_3808293
  simp only [CollatzResearch.WordTrace]
  refine ⟨138899856792212340508149533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92599904528141560338766355 138899856792212340508149533)
  ·
    refine ⟨52087446297079627690556075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138899856792212340508149533 52087446297079627690556075)
    ·
      refine ⟨78131169445619441535834113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52087446297079627690556075 78131169445619441535834113)
      ·
        refine ⟨58598377084214581151875585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78131169445619441535834113 58598377084214581151875585)
        ·
          refine ⟨43948782813160935863906689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58598377084214581151875585 43948782813160935863906689)
          ·
            refine ⟨32961587109870701897930017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43948782813160935863906689 32961587109870701897930017)
            ·
              refine ⟨24721190332403026423447513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32961587109870701897930017 24721190332403026423447513)
              ·
                refine ⟨18540892749302269817585635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24721190332403026423447513 18540892749302269817585635)
                ·
                  refine ⟨27811339123953404726378453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18540892749302269817585635 27811339123953404726378453)
                  ·
                    refine ⟨651828260717657923274495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27811339123953404726378453 651828260717657923274495)
                    ·
                      rfl

theorem cell23_3808293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3808293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808293 prefixEnd_3808293 := by exact prefixLift 3808293
  have htrace : WordTrace (prefixWord ++ tailWord_3808293) baseStart_3808293 baseEnd_3808293 := by
    simpa [prefixWord, tailWord_3808293, baseEnd_3808293] using wordTrace_append hprefix tailTrace_3808293
  have hstable : (prefixWord ++ tailWord_3808293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808293).length < 2 ^ (prefixWord ++ tailWord_3808293).sum := by decide
  have hdescent : baseEnd_3808293 < baseStart_3808293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808300 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_3808300 : Nat := 118140960795 + 3808300 * 2 ^ 59
def prefixEnd_3808300 : Nat := 4983230072969 + 3 ^ 40 * 3808300 * 2
def baseEnd_3808300 : Nat := 1955488376517555242435953

theorem tailTrace_3808300 : CollatzResearch.WordTrace tailWord_3808300 prefixEnd_3808300 1955488376517555242435953 := by
  unfold tailWord_3808300
  simp only [CollatzResearch.WordTrace]
  refine ⟨69450056051593490351827177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92600074735457987135769569 69450056051593490351827177)
  ·
    refine ⟨52087542038695117763870383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69450056051593490351827177 52087542038695117763870383)
    ·
      refine ⟨78131313058042676645805575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52087542038695117763870383 78131313058042676645805575)
      ·
        refine ⟨117196969587064014968708363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78131313058042676645805575 117196969587064014968708363)
        ·
          refine ⟨175795454380596022453062545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117196969587064014968708363 175795454380596022453062545)
          ·
            refine ⟨131846590785447016839796909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175795454380596022453062545 131846590785447016839796909)
            ·
              refine ⟨49442471544542631314923841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131846590785447016839796909 49442471544542631314923841)
              ·
                refine ⟨37081853658406973486192881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49442471544542631314923841 37081853658406973486192881)
                ·
                  refine ⟨27811390243805230114644661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37081853658406973486192881 27811390243805230114644661)
                  ·
                    refine ⟨2607317835356740323247937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27811390243805230114644661 2607317835356740323247937)
                    ·
                      refine ⟨1955488376517555242435953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607317835356740323247937 1955488376517555242435953)
                      ·
                        rfl

theorem cell23_3808300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_3808300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808300 prefixEnd_3808300 := by exact prefixLift 3808300
  have htrace : WordTrace (prefixWord ++ tailWord_3808300) baseStart_3808300 baseEnd_3808300 := by
    simpa [prefixWord, tailWord_3808300, baseEnd_3808300] using wordTrace_append hprefix tailTrace_3808300
  have hstable : (prefixWord ++ tailWord_3808300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808300).length < 2 ^ (prefixWord ++ tailWord_3808300).sum := by decide
  have hdescent : baseEnd_3808300 < baseStart_3808300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808330 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_3808330 : Nat := 118140960795 + 3808330 * 2 ^ 59
def prefixEnd_3808330 : Nat := 4983230072969 + 3 ^ 40 * 3808330 * 2
def baseEnd_3808330 : Nat := 1955503780937190125060815

theorem tailTrace_3808330 : CollatzResearch.WordTrace tailWord_3808330 prefixEnd_3808330 1955503780937190125060815 := by
  unfold tailWord_3808330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34725301573269573956811611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92600804195385530551497629 34725301573269573956811611)
  ·
    refine ⟨52087952359904360935217417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34725301573269573956811611 52087952359904360935217417)
    ·
      refine ⟨39065964269928270701413063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52087952359904360935217417 39065964269928270701413063)
      ·
        refine ⟨58598946404892406052119595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39065964269928270701413063 58598946404892406052119595)
        ·
          refine ⟨87898419607338609078179393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58598946404892406052119595 87898419607338609078179393)
          ·
            refine ⟨65923814705503956808634545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87898419607338609078179393 65923814705503956808634545)
            ·
              refine ⟨49442861029127967606475909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65923814705503956808634545 49442861029127967606475909)
              ·
                refine ⟨9270536442961493926214233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49442861029127967606475909 9270536442961493926214233)
                ·
                  refine ⟨6952902332221120444660675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9270536442961493926214233 6952902332221120444660675)
                  ·
                    refine ⟨10429353498331680666991013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6952902332221120444660675 10429353498331680666991013)
                    ·
                      refine ⟨1955503780937190125060815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10429353498331680666991013 1955503780937190125060815)
                      ·
                        rfl

theorem cell23_3808330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_3808330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808330 prefixEnd_3808330 := by exact prefixLift 3808330
  have htrace : WordTrace (prefixWord ++ tailWord_3808330) baseStart_3808330 baseEnd_3808330 := by
    simpa [prefixWord, tailWord_3808330, baseEnd_3808330] using wordTrace_append hprefix tailTrace_3808330
  have hstable : (prefixWord ++ tailWord_3808330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808330).length < 2 ^ (prefixWord ++ tailWord_3808330).sum := by decide
  have hdescent : baseEnd_3808330 < baseStart_3808330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808343 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3808343 : Nat := 118140960795 + 3808343 * 2 ^ 59
def prefixEnd_3808343 : Nat := 4983230072969 + 3 ^ 40 * 3808343 * 2
def baseEnd_3808343 : Nat := 1955510456185698574198255

theorem tailTrace_3808343 : CollatzResearch.WordTrace tailWord_3808343 prefixEnd_3808343 1955510456185698574198255 := by
  unfold tailWord_3808343
  simp only [CollatzResearch.WordTrace]
  refine ⟨138901680442031199047469683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92601120294687466031646455 138901680442031199047469683)
  ·
    refine ⟨208352520663046798571204525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138901680442031199047469683 208352520663046798571204525)
    ·
      refine ⟨78132195248642549464201697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208352520663046798571204525 78132195248642549464201697)
      ·
        refine ⟨58599146436481912098151273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78132195248642549464201697 58599146436481912098151273)
        ·
          refine ⟨43949359827361434073613455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58599146436481912098151273 43949359827361434073613455)
          ·
            refine ⟨65924039741042151110420183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43949359827361434073613455 65924039741042151110420183)
            ·
              refine ⟨98886059611563226665630275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65924039741042151110420183 98886059611563226665630275)
              ·
                refine ⟨148329089417344839998445413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98886059611563226665630275 148329089417344839998445413)
                ·
                  refine ⟨27811704265752157499708515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148329089417344839998445413 27811704265752157499708515)
                  ·
                    refine ⟨41717556398628236249562773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27811704265752157499708515 41717556398628236249562773)
                    ·
                      refine ⟨1955510456185698574198255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41717556398628236249562773 1955510456185698574198255)
                      ·
                        rfl

theorem cell23_3808343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3808343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808343 prefixEnd_3808343 := by exact prefixLift 3808343
  have htrace : WordTrace (prefixWord ++ tailWord_3808343) baseStart_3808343 baseEnd_3808343 := by
    simpa [prefixWord, tailWord_3808343, baseEnd_3808343] using wordTrace_append hprefix tailTrace_3808343
  have hstable : (prefixWord ++ tailWord_3808343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808343).length < 2 ^ (prefixWord ++ tailWord_3808343).sum := by decide
  have hdescent : baseEnd_3808343 < baseStart_3808343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808434 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3808434 : Nat := 118140960795 + 3808434 * 2 ^ 59
def prefixEnd_3808434 : Nat := 4983230072969 + 3 ^ 40 * 3808434 * 2
def baseEnd_3808434 : Nat := 651852394308419239386779

theorem tailTrace_3808434 : CollatzResearch.WordTrace tailWord_3808434 prefixEnd_3808434 651852394308419239386779 := by
  unfold tailWord_3808434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726249871175380397258089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92603332989801014392688237 34726249871175380397258089)
  ·
    refine ⟨26044687403381535297943567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34726249871175380397258089 26044687403381535297943567)
    ·
      refine ⟨39067031105072302946915351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26044687403381535297943567 39067031105072302946915351)
      ·
        refine ⟨58600546657608454420373027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39067031105072302946915351 58600546657608454420373027)
        ·
          refine ⟨87900819986412681630559541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58600546657608454420373027 87900819986412681630559541)
          ·
            refine ⟨8240701873726188902864957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87900819986412681630559541 8240701873726188902864957)
            ·
              refine ⟨3090263202647320838574359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8240701873726188902864957 3090263202647320838574359)
              ·
                refine ⟨4635394803970981257861539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090263202647320838574359 4635394803970981257861539)
                ·
                  refine ⟨6953092205956471886792309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635394803970981257861539 6953092205956471886792309)
                  ·
                    refine ⟨651852394308419239386779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6953092205956471886792309 651852394308419239386779)
                    ·
                      rfl

theorem cell23_3808434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3808434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808434 prefixEnd_3808434 := by exact prefixLift 3808434
  have htrace : WordTrace (prefixWord ++ tailWord_3808434) baseStart_3808434 baseEnd_3808434 := by
    simpa [prefixWord, tailWord_3808434, baseEnd_3808434] using wordTrace_append hprefix tailTrace_3808434
  have hstable : (prefixWord ++ tailWord_3808434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808434).length < 2 ^ (prefixWord ++ tailWord_3808434).sum := by decide
  have hdescent : baseEnd_3808434 < baseStart_3808434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808440 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_3808440 : Nat := 118140960795 + 3808440 * 2 ^ 59
def prefixEnd_3808440 : Nat := 4983230072969 + 3 ^ 40 * 3808440 * 2
def baseEnd_3808440 : Nat := 1955560263809184694685309

theorem tailTrace_3808440 : CollatzResearch.WordTrace tailWord_3808440 prefixEnd_3808440 1955560263809184694685309 := by
  unfold tailWord_3808440
  simp only [CollatzResearch.WordTrace]
  refine ⟨69452609161339892306875387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92603478881786523075833849 69452609161339892306875387)
  ·
    refine ⟨104178913742009838460313081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69452609161339892306875387 104178913742009838460313081)
    ·
      refine ⟨78134185306507378845234811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104178913742009838460313081 78134185306507378845234811)
      ·
        refine ⟨117201277959761068267852217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78134185306507378845234811 117201277959761068267852217)
        ·
          refine ⟨87900958469820801200889163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117201277959761068267852217 87900958469820801200889163)
          ·
            refine ⟨131851437704731201801333745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87900958469820801200889163 131851437704731201801333745)
            ·
              refine ⟨98888578278548401351000309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131851437704731201801333745 98888578278548401351000309)
              ·
                refine ⟨9270804213613912626656279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98888578278548401351000309 9270804213613912626656279)
                ·
                  refine ⟨13906206320420868939984419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9270804213613912626656279 13906206320420868939984419)
                  ·
                    refine ⟨20859309480631303409976629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13906206320420868939984419 20859309480631303409976629)
                    ·
                      refine ⟨1955560263809184694685309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20859309480631303409976629 1955560263809184694685309)
                      ·
                        rfl

theorem cell23_3808440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_3808440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808440 prefixEnd_3808440 := by exact prefixLift 3808440
  have htrace : WordTrace (prefixWord ++ tailWord_3808440) baseStart_3808440 baseEnd_3808440 := by
    simpa [prefixWord, tailWord_3808440, baseEnd_3808440] using wordTrace_append hprefix tailTrace_3808440
  have hstable : (prefixWord ++ tailWord_3808440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808440).length < 2 ^ (prefixWord ++ tailWord_3808440).sum := by decide
  have hdescent : baseEnd_3808440 < baseStart_3808440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808447 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 2, 4]
def baseStart_3808447 : Nat := 118140960795 + 3808447 * 2 ^ 59
def prefixEnd_3808447 : Nat := 4983230072969 + 3 ^ 40 * 3808447 * 2
def baseEnd_3808447 : Nat := 651854619391255389099259

theorem tailTrace_3808447 : CollatzResearch.WordTrace tailWord_3808447 prefixEnd_3808447 651854619391255389099259 := by
  unfold tailWord_3808447
  simp only [CollatzResearch.WordTrace]
  refine ⟨138905473633654424809255595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92603649089102949872837063 138905473633654424809255595)
  ·
    refine ⟨208358210450481637213883393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138905473633654424809255595 208358210450481637213883393)
    ·
      refine ⟨156268657837861227910412545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208358210450481637213883393 156268657837861227910412545)
      ·
        refine ⟨117201493378395920932809409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156268657837861227910412545 117201493378395920932809409)
        ·
          refine ⟨87901120033796940699607057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117201493378395920932809409 87901120033796940699607057)
          ·
            refine ⟨65925840025347705524705293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87901120033796940699607057 65925840025347705524705293)
            ·
              refine ⟨24722190009505389571764485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65925840025347705524705293 24722190009505389571764485)
              ·
                refine ⟨4635410626782260544705841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24722190009505389571764485 4635410626782260544705841)
                ·
                  refine ⟨3476557970086695408529381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635410626782260544705841 3476557970086695408529381)
                  ·
                    refine ⟨651854619391255389099259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476557970086695408529381 651854619391255389099259)
                    ·
                      rfl

theorem cell23_3808447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_3808447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808447 prefixEnd_3808447 := by exact prefixLift 3808447
  have htrace : WordTrace (prefixWord ++ tailWord_3808447) baseStart_3808447 baseEnd_3808447 := by
    simpa [prefixWord, tailWord_3808447, baseEnd_3808447] using wordTrace_append hprefix tailTrace_3808447
  have hstable : (prefixWord ++ tailWord_3808447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808447).length < 2 ^ (prefixWord ++ tailWord_3808447).sum := by decide
  have hdescent : baseEnd_3808447 < baseStart_3808447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808488 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3808488 : Nat := 118140960795 + 3808488 * 2 ^ 59
def prefixEnd_3808488 : Nat := 4983230072969 + 3 ^ 40 * 3808488 * 2
def baseEnd_3808488 : Nat := 1955584910880600506885089

theorem tailTrace_3808488 : CollatzResearch.WordTrace tailWord_3808488 prefixEnd_3808488 1955584910880600506885089 := by
  unfold tailWord_3808488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69453484513252944405749059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92604646017670592540998745 69453484513252944405749059)
  ·
    refine ⟨104180226769879416608623589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69453484513252944405749059 104180226769879416608623589)
    ·
      refine ⟨19533792519352390614116923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104180226769879416608623589 19533792519352390614116923)
      ·
        refine ⟨29300688779028585921175385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19533792519352390614116923 29300688779028585921175385)
        ·
          refine ⟨21975516584271439440881539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29300688779028585921175385 21975516584271439440881539)
          ·
            refine ⟨32963274876407159161322309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975516584271439440881539 32963274876407159161322309)
            ·
              refine ⟨6180614039326342342747933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32963274876407159161322309 6180614039326342342747933)
              ·
                refine ⟨2317730264747378378530475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6180614039326342342747933 2317730264747378378530475)
                ·
                  refine ⟨3476595397121067567795713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317730264747378378530475 3476595397121067567795713)
                  ·
                    refine ⟨2607446547840800675846785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476595397121067567795713 2607446547840800675846785)
                    ·
                      refine ⟨1955584910880600506885089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607446547840800675846785 1955584910880600506885089)
                      ·
                        rfl

theorem cell23_3808488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3808488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808488 prefixEnd_3808488 := by exact prefixLift 3808488
  have htrace : WordTrace (prefixWord ++ tailWord_3808488) baseStart_3808488 baseEnd_3808488 := by
    simpa [prefixWord, tailWord_3808488, baseEnd_3808488] using wordTrace_append hprefix tailTrace_3808488
  have hstable : (prefixWord ++ tailWord_3808488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808488).length < 2 ^ (prefixWord ++ tailWord_3808488).sum := by decide
  have hdescent : baseEnd_3808488 < baseStart_3808488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808491 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 1, 2, 3]
def baseStart_3808491 : Nat := 118140960795 + 3808491 * 2 ^ 59
def prefixEnd_3808491 : Nat := 4983230072969 + 3 ^ 40 * 3808491 * 2
def baseEnd_3808491 : Nat := 1955586451322563995147575

theorem tailTrace_3808491 : CollatzResearch.WordTrace tailWord_3808491 prefixEnd_3808491 1955586451322563995147575 := by
  unfold tailWord_3808491
  simp only [CollatzResearch.WordTrace]
  refine ⟨138907078445495020323857327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92604718963663346882571551 138907078445495020323857327)
  ·
    refine ⟨208360617668242530485785991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138907078445495020323857327 208360617668242530485785991)
    ·
      refine ⟨312540926502363795728678987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208360617668242530485785991 312540926502363795728678987)
      ·
        refine ⟨468811389753545693593018481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312540926502363795728678987 468811389753545693593018481)
        ·
          refine ⟨351608542315159270194763861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468811389753545693593018481 351608542315159270194763861)
          ·
            refine ⟨4120412605255772697594889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 351608542315159270194763861 4120412605255772697594889)
            ·
              refine ⟨3090309453941829523196167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120412605255772697594889 3090309453941829523196167)
              ·
                refine ⟨4635464180912744284794251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090309453941829523196167 4635464180912744284794251)
                ·
                  refine ⟨6953196271369116427191377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635464180912744284794251 6953196271369116427191377)
                  ·
                    refine ⟨5214897203526837320393533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6953196271369116427191377 5214897203526837320393533)
                    ·
                      refine ⟨1955586451322563995147575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214897203526837320393533 1955586451322563995147575)
                      ·
                        rfl

theorem cell23_3808491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 2, 3].length) (baseStart_3808491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808491 prefixEnd_3808491 := by exact prefixLift 3808491
  have htrace : WordTrace (prefixWord ++ tailWord_3808491) baseStart_3808491 baseEnd_3808491 := by
    simpa [prefixWord, tailWord_3808491, baseEnd_3808491] using wordTrace_append hprefix tailTrace_3808491
  have hstable : (prefixWord ++ tailWord_3808491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808491).length < 2 ^ (prefixWord ++ tailWord_3808491).sum := by decide
  have hdescent : baseEnd_3808491 < baseStart_3808491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808498 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3808498 : Nat := 118140960795 + 3808498 * 2 ^ 59
def prefixEnd_3808498 : Nat := 4983230072969 + 3 ^ 40 * 3808498 * 2
def baseEnd_3808498 : Nat := 651863348562381822586681

theorem tailTrace_3808498 : CollatzResearch.WordTrace tailWord_3808498 prefixEnd_3808498 651863348562381822586681 := by
  unfold tailWord_3808498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34726833439117415129840537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92604889170979773679574765 34726833439117415129840537)
  ·
    refine ⟨26045125079338061347380403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34726833439117415129840537 26045125079338061347380403)
    ·
      refine ⟨39067687619007092021070605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26045125079338061347380403 39067687619007092021070605)
      ·
        refine ⟨14650382857127659507901477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39067687619007092021070605 14650382857127659507901477)
        ·
          refine ⟨2746946785711436157731527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14650382857127659507901477 2746946785711436157731527)
          ·
            refine ⟨4120420178567154236597291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746946785711436157731527 4120420178567154236597291)
            ·
              refine ⟨6180630267850731354895937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120420178567154236597291 6180630267850731354895937)
              ·
                refine ⟨4635472700888048516171953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180630267850731354895937 4635472700888048516171953)
                ·
                  refine ⟨3476604525666036387128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635472700888048516171953 3476604525666036387128965)
                  ·
                    refine ⟨651863348562381822586681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476604525666036387128965 651863348562381822586681)
                    ·
                      rfl

theorem cell23_3808498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3808498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808498 prefixEnd_3808498 := by exact prefixLift 3808498
  have htrace : WordTrace (prefixWord ++ tailWord_3808498) baseStart_3808498 baseEnd_3808498 := by
    simpa [prefixWord, tailWord_3808498, baseEnd_3808498] using wordTrace_append hprefix tailTrace_3808498
  have hstable : (prefixWord ++ tailWord_3808498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808498).length < 2 ^ (prefixWord ++ tailWord_3808498).sum := by decide
  have hdescent : baseEnd_3808498 < baseStart_3808498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808521 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 2, 1, 3]
def baseStart_3808521 : Nat := 118140960795 + 3808521 * 2 ^ 59
def prefixEnd_3808521 : Nat := 4983230072969 + 3 ^ 40 * 3808521 * 2
def baseEnd_3808521 : Nat := 1955601855742198877772437

theorem tailTrace_3808521 : CollatzResearch.WordTrace tailWord_3808521 prefixEnd_3808521 1955601855742198877772437 := by
  unfold tailWord_3808521
  simp only [CollatzResearch.WordTrace]
  refine ⟨138908172635386335447449417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92605448423590890298299611 138908172635386335447449417)
  ·
    refine ⟨104181129476539751585587063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138908172635386335447449417 104181129476539751585587063)
    ·
      refine ⟨156271694214809627378380595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104181129476539751585587063 156271694214809627378380595)
      ·
        refine ⟨234407541322214441067570893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156271694214809627378380595 234407541322214441067570893)
        ·
          refine ⟨87902827995830415400339085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234407541322214441067570893 87902827995830415400339085)
          ·
            refine ⟨32963560498436405775127157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87902827995830415400339085 32963560498436405775127157)
            ·
              refine ⟨3090333796728413041418171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32963560498436405775127157 3090333796728413041418171)
              ·
                refine ⟨4635500695092619562127257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090333796728413041418171 4635500695092619562127257)
                ·
                  refine ⟨3476625521319464671595443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635500695092619562127257 3476625521319464671595443)
                  ·
                    refine ⟨5214938281979197007393165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476625521319464671595443 5214938281979197007393165)
                    ·
                      refine ⟨1955601855742198877772437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214938281979197007393165 1955601855742198877772437)
                      ·
                        rfl

theorem cell23_3808521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 1, 3].length) (baseStart_3808521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808521 prefixEnd_3808521 := by exact prefixLift 3808521
  have htrace : WordTrace (prefixWord ++ tailWord_3808521) baseStart_3808521 baseEnd_3808521 := by
    simpa [prefixWord, tailWord_3808521, baseEnd_3808521] using wordTrace_append hprefix tailTrace_3808521
  have hstable : (prefixWord ++ tailWord_3808521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808521).length < 2 ^ (prefixWord ++ tailWord_3808521).sum := by decide
  have hdescent : baseEnd_3808521 < baseStart_3808521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808547 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3808547 : Nat := 118140960795 + 3808547 * 2 ^ 59
def prefixEnd_3808547 : Nat := 4983230072969 + 3 ^ 40 * 3808547 * 2
def baseEnd_3808547 : Nat := 1955615206239215776047317

theorem tailTrace_3808547 : CollatzResearch.WordTrace tailWord_3808547 prefixEnd_3808547 1955615206239215776047317 := by
  unfold tailWord_3808547
  simp only [CollatzResearch.WordTrace]
  refine ⟨138909120933292141887895895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92606080622194761258597263 138909120933292141887895895)
  ·
    refine ⟨208363681399938212831843843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138909120933292141887895895 208363681399938212831843843)
    ·
      refine ⟨312545522099907319247765765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208363681399938212831843843 312545522099907319247765765)
      ·
        refine ⟨58602285393732622358956081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312545522099907319247765765 58602285393732622358956081)
        ·
          refine ⟨43951714045299466769217061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58602285393732622358956081 43951714045299466769217061)
          ·
            refine ⟨8240946383493650019228199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43951714045299466769217061 8240946383493650019228199)
            ·
              refine ⟨12361419575240475028842299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240946383493650019228199 12361419575240475028842299)
              ·
                refine ⟨18542129362860712543263449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361419575240475028842299 18542129362860712543263449)
                ·
                  refine ⟨13906597022145534407447587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18542129362860712543263449 13906597022145534407447587)
                  ·
                    refine ⟨20859895533218301611171381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13906597022145534407447587 20859895533218301611171381)
                    ·
                      refine ⟨1955615206239215776047317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20859895533218301611171381 1955615206239215776047317)
                      ·
                        rfl

theorem cell23_3808547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3808547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808547 prefixEnd_3808547 := by exact prefixLift 3808547
  have htrace : WordTrace (prefixWord ++ tailWord_3808547) baseStart_3808547 baseEnd_3808547 := by
    simpa [prefixWord, tailWord_3808547, baseEnd_3808547] using wordTrace_append hprefix tailTrace_3808547
  have hstable : (prefixWord ++ tailWord_3808547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808547).length < 2 ^ (prefixWord ++ tailWord_3808547).sum := by decide
  have hdescent : baseEnd_3808547 < baseStart_3808547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808560 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_3808560 : Nat := 118140960795 + 3808560 * 2 ^ 59
def prefixEnd_3808560 : Nat := 4983230072969 + 3 ^ 40 * 3808560 * 2
def baseEnd_3808560 : Nat := 1955621881487724225184757

theorem tailTrace_3808560 : CollatzResearch.WordTrace tailWord_3808560 prefixEnd_3808560 1955621881487724225184757 := by
  unfold tailWord_3808560
  simp only [CollatzResearch.WordTrace]
  refine ⟨69454797541122522554059567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92606396721496696738746089 69454797541122522554059567)
  ·
    refine ⟨104182196311683783831089351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69454797541122522554059567 104182196311683783831089351)
    ·
      refine ⟨156273294467525675746634027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104182196311683783831089351 156273294467525675746634027)
      ·
        refine ⟨234409941701288513619951041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156273294467525675746634027 234409941701288513619951041)
        ·
          refine ⟨175807456275966385214963281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234409941701288513619951041 175807456275966385214963281)
          ·
            refine ⟨131855592206974788911222461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175807456275966385214963281 131855592206974788911222461)
            ·
              refine ⟨49445847077615545841708423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131855592206974788911222461 49445847077615545841708423)
              ·
                refine ⟨74168770616423318762562635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49445847077615545841708423 74168770616423318762562635)
                ·
                  refine ⟨111253155924634978143843953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74168770616423318762562635 111253155924634978143843953)
                  ·
                    refine ⟨83439866943476233607882965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111253155924634978143843953 83439866943476233607882965)
                    ·
                      refine ⟨1955621881487724225184757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83439866943476233607882965 1955621881487724225184757)
                      ·
                        rfl

theorem cell23_3808560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_3808560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808560 prefixEnd_3808560 := by exact prefixLift 3808560
  have htrace : WordTrace (prefixWord ++ tailWord_3808560) baseStart_3808560 baseEnd_3808560 := by
    simpa [prefixWord, tailWord_3808560, baseEnd_3808560] using wordTrace_append hprefix tailTrace_3808560
  have hstable : (prefixWord ++ tailWord_3808560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808560).length < 2 ^ (prefixWord ++ tailWord_3808560).sum := by decide
  have hdescent : baseEnd_3808560 < baseStart_3808560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808561 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_3808561 : Nat := 118140960795 + 3808561 * 2 ^ 59
def prefixEnd_3808561 : Nat := 4983230072969 + 3 ^ 40 * 3808561 * 2
def baseEnd_3808561 : Nat := 1955622394968378721272253

theorem tailTrace_3808561 : CollatzResearch.WordTrace tailWord_3808561 prefixEnd_3808561 1955622394968378721272253 := by
  unfold tailWord_3808561
  simp only [CollatzResearch.WordTrace]
  refine ⟨138909631555241422278905537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92606421036827614852603691 138909631555241422278905537)
  ·
    refine ⟨104182223666431066709179153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138909631555241422278905537 104182223666431066709179153)
    ·
      refine ⟨78136667749823300031884365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104182223666431066709179153 78136667749823300031884365)
      ·
        refine ⟨29301250406183737511956637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78136667749823300031884365 29301250406183737511956637)
        ·
          refine ⟨10987968902318901566983739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29301250406183737511956637 10987968902318901566983739)
          ·
            refine ⟨16481953353478352350475609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987968902318901566983739 16481953353478352350475609)
            ·
              refine ⟨12361465015108764262856707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16481953353478352350475609 12361465015108764262856707)
              ·
                refine ⟨18542197522663146394285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361465015108764262856707 18542197522663146394285061)
                ·
                  refine ⟨3476662035499339948928449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18542197522663146394285061 3476662035499339948928449)
                  ·
                    refine ⟨2607496526624504961696337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476662035499339948928449 2607496526624504961696337)
                    ·
                      refine ⟨1955622394968378721272253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607496526624504961696337 1955622394968378721272253)
                      ·
                        rfl

theorem cell23_3808561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_3808561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808561 prefixEnd_3808561 := by exact prefixLift 3808561
  have htrace : WordTrace (prefixWord ++ tailWord_3808561) baseStart_3808561 baseEnd_3808561 := by
    simpa [prefixWord, tailWord_3808561, baseEnd_3808561] using wordTrace_append hprefix tailTrace_3808561
  have hstable : (prefixWord ++ tailWord_3808561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808561).length < 2 ^ (prefixWord ++ tailWord_3808561).sum := by decide
  have hdescent : baseEnd_3808561 < baseStart_3808561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808564 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3808564 : Nat := 118140960795 + 3808564 * 2 ^ 59
def prefixEnd_3808564 : Nat := 4983230072969 + 3 ^ 40 * 3808564 * 2
def baseEnd_3808564 : Nat := 1955623935410342209534739

theorem tailTrace_3808564 : CollatzResearch.WordTrace tailWord_3808564 prefixEnd_3808564 1955623935410342209534739 := by
  unfold tailWord_3808564
  simp only [CollatzResearch.WordTrace]
  refine ⟨69454870487115276895632373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92606493982820369194176497 69454870487115276895632373)
  ·
    refine ⟨6511394108167057208965535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69454870487115276895632373 6511394108167057208965535)
    ·
      refine ⟨9767091162250585813448303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511394108167057208965535 9767091162250585813448303)
      ·
        refine ⟨14650636743375878720172455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9767091162250585813448303 14650636743375878720172455)
        ·
          refine ⟨21975955115063818080258683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14650636743375878720172455 21975955115063818080258683)
          ·
            refine ⟨32963932672595727120388025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975955115063818080258683 32963932672595727120388025)
            ·
              refine ⟨24722949504446795340291019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32963932672595727120388025 24722949504446795340291019)
              ·
                refine ⟨37084424256670193010436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24722949504446795340291019 37084424256670193010436529)
                ·
                  refine ⟨27813318192502644757827397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37084424256670193010436529 27813318192502644757827397)
                  ·
                    refine ⟨5214997161094245892092637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27813318192502644757827397 5214997161094245892092637)
                    ·
                      refine ⟨1955623935410342209534739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5214997161094245892092637 1955623935410342209534739)
                      ·
                        rfl

theorem cell23_3808564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3808564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808564 prefixEnd_3808564 := by exact prefixLift 3808564
  have htrace : WordTrace (prefixWord ++ tailWord_3808564) baseStart_3808564 baseEnd_3808564 := by
    simpa [prefixWord, tailWord_3808564, baseEnd_3808564] using wordTrace_append hprefix tailTrace_3808564
  have hstable : (prefixWord ++ tailWord_3808564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808564).length < 2 ^ (prefixWord ++ tailWord_3808564).sum := by decide
  have hdescent : baseEnd_3808564 < baseStart_3808564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808617 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_3808617 : Nat := 118140960795 + 3808617 * 2 ^ 59
def prefixEnd_3808617 : Nat := 4983230072969 + 3 ^ 40 * 3808617 * 2
def baseEnd_3808617 : Nat := 1955651149885030502171995

theorem tailTrace_3808617 : CollatzResearch.WordTrace tailWord_3808617 prefixEnd_3808617 1955651149885030502171995 := by
  unfold tailWord_3808617
  simp only [CollatzResearch.WordTrace]
  refine ⟨138911674043038543842944105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92607782695359029228629403 138911674043038543842944105)
  ·
    refine ⟨104183755532278907882208079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138911674043038543842944105 104183755532278907882208079)
    ·
      refine ⟨156275633298418361823312119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104183755532278907882208079 156275633298418361823312119)
      ·
        refine ⟨234413449947627542734968179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156275633298418361823312119 234413449947627542734968179)
        ·
          refine ⟨351620174921441314102452269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234413449947627542734968179 351620174921441314102452269)
          ·
            refine ⟨131857565595540492788419601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351620174921441314102452269 131857565595540492788419601)
            ·
              refine ⟨98893174196655369591314701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131857565595540492788419601 98893174196655369591314701)
              ·
                refine ⟨37084940323745763596743013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98893174196655369591314701 37084940323745763596743013)
                ·
                  refine ⟨6953426310702330674389315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37084940323745763596743013 6953426310702330674389315)
                  ·
                    refine ⟨10430139466053496011583973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953426310702330674389315 10430139466053496011583973)
                    ·
                      refine ⟨1955651149885030502171995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10430139466053496011583973 1955651149885030502171995)
                      ·
                        rfl

theorem cell23_3808617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_3808617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808617 prefixEnd_3808617 := by exact prefixLift 3808617
  have htrace : WordTrace (prefixWord ++ tailWord_3808617) baseStart_3808617 baseEnd_3808617 := by
    simpa [prefixWord, tailWord_3808617, baseEnd_3808617] using wordTrace_append hprefix tailTrace_3808617
  have hstable : (prefixWord ++ tailWord_3808617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808617).length < 2 ^ (prefixWord ++ tailWord_3808617).sum := by decide
  have hdescent : baseEnd_3808617 < baseStart_3808617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808634 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_3808634 : Nat := 118140960795 + 3808634 * 2 ^ 59
def prefixEnd_3808634 : Nat := 4983230072969 + 3 ^ 40 * 3808634 * 2
def baseEnd_3808634 : Nat := 1955659879056156935659417

theorem tailTrace_3808634 : CollatzResearch.WordTrace tailWord_3808634 prefixEnd_3808634 1955659879056156935659417 := by
  unfold tailWord_3808634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728073520994238936578239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92608196055984637164208637 34728073520994238936578239)
  ·
    refine ⟨52092110281491358404867359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34728073520994238936578239 52092110281491358404867359)
    ·
      refine ⟨78138165422237037607301039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52092110281491358404867359 78138165422237037607301039)
      ·
        refine ⟨117207248133355556410951559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78138165422237037607301039 117207248133355556410951559)
        ·
          refine ⟨175810872200033334616427339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117207248133355556410951559 175810872200033334616427339)
          ·
            refine ⟨263716308300050001924641009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175810872200033334616427339 263716308300050001924641009)
            ·
              refine ⟨197787231225037501443480757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263716308300050001924641009 197787231225037501443480757)
              ·
                refine ⟨18542552927347265760326321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197787231225037501443480757 18542552927347265760326321)
                ·
                  refine ⟨13906914695510449320244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18542552927347265760326321 13906914695510449320244741)
                  ·
                    refine ⟨2607546505408209247545889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13906914695510449320244741 2607546505408209247545889)
                    ·
                      refine ⟨1955659879056156935659417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607546505408209247545889 1955659879056156935659417)
                      ·
                        rfl

theorem cell23_3808634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_3808634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808634 prefixEnd_3808634 := by exact prefixLift 3808634
  have htrace : WordTrace (prefixWord ++ tailWord_3808634) baseStart_3808634 baseEnd_3808634 := by
    simpa [prefixWord, tailWord_3808634, baseEnd_3808634] using wordTrace_append hprefix tailTrace_3808634
  have hstable : (prefixWord ++ tailWord_3808634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808634).length < 2 ^ (prefixWord ++ tailWord_3808634).sum := by decide
  have hdescent : baseEnd_3808634 < baseStart_3808634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808644 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3808644 : Nat := 118140960795 + 3808644 * 2 ^ 59
def prefixEnd_3808644 : Nat := 4983230072969 + 3 ^ 40 * 3808644 * 2
def baseEnd_3808644 : Nat := 651888337954233965511457

theorem tailTrace_3808644 : CollatzResearch.WordTrace tailWord_3808644 prefixEnd_3808644 651888337954233965511457 := by
  unfold tailWord_3808644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69456329406970363727088493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92608439209293818302784657 69456329406970363727088493)
  ·
    refine ⟨26046123527613886397658185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69456329406970363727088493 26046123527613886397658185)
    ·
      refine ⟨19534592645710414798243639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26046123527613886397658185 19534592645710414798243639)
      ·
        refine ⟨29301888968565622197365459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534592645710414798243639 29301888968565622197365459)
        ·
          refine ⟨43952833452848433296048189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29301888968565622197365459 43952833452848433296048189)
          ·
            refine ⟨16482312544818162486018071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43952833452848433296048189 16482312544818162486018071)
            ·
              refine ⟨24723468817227243729027107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16482312544818162486018071 24723468817227243729027107)
              ·
                refine ⟨37085203225840865593540661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24723468817227243729027107 37085203225840865593540661)
                ·
                  refine ⟨3476737802422581149394437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37085203225840865593540661 3476737802422581149394437)
                  ·
                    refine ⟨651888337954233965511457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476737802422581149394437 651888337954233965511457)
                    ·
                      rfl

theorem cell23_3808644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3808644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808644 prefixEnd_3808644 := by exact prefixLift 3808644
  have htrace : WordTrace (prefixWord ++ tailWord_3808644) baseStart_3808644 baseEnd_3808644 := by
    simpa [prefixWord, tailWord_3808644, baseEnd_3808644] using wordTrace_append hprefix tailTrace_3808644
  have hstable : (prefixWord ++ tailWord_3808644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808644).length < 2 ^ (prefixWord ++ tailWord_3808644).sum := by decide
  have hdescent : baseEnd_3808644 < baseStart_3808644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808661 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3808661 : Nat := 118140960795 + 3808661 * 2 ^ 59
def prefixEnd_3808661 : Nat := 4983230072969 + 3 ^ 40 * 3808661 * 2
def baseEnd_3808661 : Nat := 651891247677942776673931

theorem tailTrace_3808661 : CollatzResearch.WordTrace tailWord_3808661 prefixEnd_3808661 651891247677942776673931 := by
  unfold tailWord_3808661
  simp only [CollatzResearch.WordTrace]
  refine ⟨138913278854879139357545837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92608852569919426238363891 138913278854879139357545837)
  ·
    refine ⟨52092479570579677259079689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138913278854879139357545837 52092479570579677259079689)
    ·
      refine ⟨39069359677934757944309767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52092479570579677259079689 39069359677934757944309767)
      ·
        refine ⟨58604039516902136916464651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39069359677934757944309767 58604039516902136916464651)
        ·
          refine ⟨87906059275353205374696977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58604039516902136916464651 87906059275353205374696977)
          ·
            refine ⟨65929544456514904031022733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87906059275353205374696977 65929544456514904031022733)
            ·
              refine ⟨24723579171193089011633525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65929544456514904031022733 24723579171193089011633525)
              ·
                refine ⟨2317835547299352094840643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24723579171193089011633525 2317835547299352094840643)
                ·
                  refine ⟨3476753320949028142260965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317835547299352094840643 3476753320949028142260965)
                  ·
                    refine ⟨651891247677942776673931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476753320949028142260965 651891247677942776673931)
                    ·
                      rfl

theorem cell23_3808661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3808661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808661 prefixEnd_3808661 := by exact prefixLift 3808661
  have htrace : WordTrace (prefixWord ++ tailWord_3808661) baseStart_3808661 baseEnd_3808661 := by
    simpa [prefixWord, tailWord_3808661, baseEnd_3808661] using wordTrace_append hprefix tailTrace_3808661
  have hstable : (prefixWord ++ tailWord_3808661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808661).length < 2 ^ (prefixWord ++ tailWord_3808661).sum := by decide
  have hdescent : baseEnd_3808661 < baseStart_3808661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3]
def baseStart_3808667 : Nat := 118140960795 + 3808667 * 2 ^ 59
def prefixEnd_3808667 : Nat := 4983230072969 + 3 ^ 40 * 3808667 * 2
def baseEnd_3808667 : Nat := 1955676823917755306546765

theorem tailTrace_3808667 : CollatzResearch.WordTrace tailWord_3808667 prefixEnd_3808667 1955676823917755306546765 := by
  unfold tailWord_3808667
  simp only [CollatzResearch.WordTrace]
  refine ⟨138913497692857402382264255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92608998461904934921509503 138913497692857402382264255)
  ·
    refine ⟨208370246539286103573396383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138913497692857402382264255 208370246539286103573396383)
    ·
      refine ⟨312555369808929155360094575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208370246539286103573396383 312555369808929155360094575)
      ·
        refine ⟨468833054713393733040141863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312555369808929155360094575 468833054713393733040141863)
        ·
          refine ⟨703249582070090599560212795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468833054713393733040141863 703249582070090599560212795)
          ·
            refine ⟨1054874373105135899340319193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703249582070090599560212795 1054874373105135899340319193)
            ·
              refine ⟨791155779828851924505239395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054874373105135899340319193 791155779828851924505239395)
              ·
                refine ⟨1186733669743277886757859093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791155779828851924505239395 1186733669743277886757859093)
                ·
                  refine ⟨55628140769216150941774645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1186733669743277886757859093 55628140769216150941774645)
                  ·
                    refine ⟨5215138197114014150791373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55628140769216150941774645 5215138197114014150791373)
                    ·
                      refine ⟨1955676823917755306546765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5215138197114014150791373 1955676823917755306546765)
                      ·
                        rfl

theorem cell23_3808667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 3].length) (baseStart_3808667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808667 prefixEnd_3808667 := by exact prefixLift 3808667
  have htrace : WordTrace (prefixWord ++ tailWord_3808667) baseStart_3808667 baseEnd_3808667 := by
    simpa [prefixWord, tailWord_3808667, baseEnd_3808667] using wordTrace_append hprefix tailTrace_3808667
  have hstable : (prefixWord ++ tailWord_3808667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808667).length < 2 ^ (prefixWord ++ tailWord_3808667).sum := by decide
  have hdescent : baseEnd_3808667 < baseStart_3808667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808674 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3808674 : Nat := 118140960795 + 3808674 * 2 ^ 59
def prefixEnd_3808674 : Nat := 4983230072969 + 3 ^ 40 * 3808674 * 2
def baseEnd_3808674 : Nat := 217297824253592975462137

theorem tailTrace_3808674 : CollatzResearch.WordTrace tailWord_3808674 prefixEnd_3808674 217297824253592975462137 := by
  unfold tailWord_3808674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34728438250958010644442269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92609168669221361718512717 34728438250958010644442269)
  ·
    refine ⟨13023164344109253991665851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34728438250958010644442269 13023164344109253991665851)
    ·
      refine ⟨19534746516163880987498777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023164344109253991665851 19534746516163880987498777)
      ·
        refine ⟨14651059887122910740624083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19534746516163880987498777 14651059887122910740624083)
        ·
          refine ⟨21976589830684366110936125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14651059887122910740624083 21976589830684366110936125)
          ·
            refine ⟨8241221186506637291601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21976589830684366110936125 8241221186506637291601047)
            ·
              refine ⟨12361831779759955937401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241221186506637291601047 12361831779759955937401571)
              ·
                refine ⟨18542747669639933906102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12361831779759955937401571 18542747669639933906102357)
                ·
                  refine ⟨217297824253592975462137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18542747669639933906102357 217297824253592975462137)
                  ·
                    rfl

theorem cell23_3808674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3808674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808674 prefixEnd_3808674 := by exact prefixLift 3808674
  have htrace : WordTrace (prefixWord ++ tailWord_3808674) baseStart_3808674 baseEnd_3808674 := by
    simpa [prefixWord, tailWord_3808674, baseEnd_3808674] using wordTrace_append hprefix tailTrace_3808674
  have hstable : (prefixWord ++ tailWord_3808674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808674).length < 2 ^ (prefixWord ++ tailWord_3808674).sum := by decide
  have hdescent : baseEnd_3808674 < baseStart_3808674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808687 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 5, 5]
def baseStart_3808687 : Nat := 118140960795 + 3808687 * 2 ^ 59
def prefixEnd_3808687 : Nat := 4983230072969 + 3 ^ 40 * 3808687 * 2
def baseEnd_3808687 : Nat := 651895697843615076098891

theorem tailTrace_3808687 : CollatzResearch.WordTrace tailWord_3808687 prefixEnd_3808687 651895697843615076098891 := by
  unfold tailWord_3808687
  simp only [CollatzResearch.WordTrace]
  refine ⟨138914227152784945797992315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92609484768523297198661543 138914227152784945797992315)
  ·
    refine ⟨208371340729177418696988473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138914227152784945797992315 208371340729177418696988473)
    ·
      refine ⟨156278505546883064022741355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208371340729177418696988473 156278505546883064022741355)
      ·
        refine ⟨234417758320324596034112033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156278505546883064022741355 234417758320324596034112033)
        ·
          refine ⟨175813318740243447025584025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234417758320324596034112033 175813318740243447025584025)
          ·
            refine ⟨131859989055182585269188019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175813318740243447025584025 131859989055182585269188019)
            ·
              refine ⟨197789983582773877903782029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131859989055182585269188019 197789983582773877903782029)
              ·
                refine ⟨74171243843540204213918261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197789983582773877903782029 74171243843540204213918261)
                ·
                  refine ⟨6953554110331894145054837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74171243843540204213918261 6953554110331894145054837)
                  ·
                    refine ⟨651895697843615076098891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6953554110331894145054837 651895697843615076098891)
                    ·
                      rfl

theorem cell23_3808687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_3808687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808687 prefixEnd_3808687 := by exact prefixLift 3808687
  have htrace : WordTrace (prefixWord ++ tailWord_3808687) baseStart_3808687 baseEnd_3808687 := by
    simpa [prefixWord, tailWord_3808687, baseEnd_3808687] using wordTrace_append hprefix tailTrace_3808687
  have hstable : (prefixWord ++ tailWord_3808687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808687).length < 2 ^ (prefixWord ++ tailWord_3808687).sum := by decide
  have hdescent : baseEnd_3808687 < baseStart_3808687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808701 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3808701 : Nat := 118140960795 + 3808701 * 2 ^ 59
def prefixEnd_3808701 : Nat := 4983230072969 + 3 ^ 40 * 3808701 * 2
def baseEnd_3808701 : Nat := 1955694282260008173521609

theorem tailTrace_3808701 : CollatzResearch.WordTrace tailWord_3808701 prefixEnd_3808701 1955694282260008173521609 := by
  unfold tailWord_3808701
  simp only [CollatzResearch.WordTrace]
  refine ⟨138914737774734226189001957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92609825183156150792667971 138914737774734226189001957)
  ·
    refine ⟨26046513332762667410437867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138914737774734226189001957 26046513332762667410437867)
    ·
      refine ⟨39069769999144001115656801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26046513332762667410437867 39069769999144001115656801)
      ·
        refine ⟨29302327499358000836742601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39069769999144001115656801 29302327499358000836742601)
        ·
          refine ⟨21976745624518500627556951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29302327499358000836742601 21976745624518500627556951)
          ·
            refine ⟨32965118436777750941335427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21976745624518500627556951 32965118436777750941335427)
            ·
              refine ⟨49447677655166626412003141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32965118436777750941335427 49447677655166626412003141)
              ·
                refine ⟨9271439560343742452250589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49447677655166626412003141 9271439560343742452250589)
                ·
                  refine ⟨3476789835128903419593971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9271439560343742452250589 3476789835128903419593971)
                  ·
                    refine ⟨5215184752693355129390957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476789835128903419593971 5215184752693355129390957)
                    ·
                      refine ⟨1955694282260008173521609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5215184752693355129390957 1955694282260008173521609)
                      ·
                        rfl

theorem cell23_3808701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3808701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808701 prefixEnd_3808701 := by exact prefixLift 3808701
  have htrace : WordTrace (prefixWord ++ tailWord_3808701) baseStart_3808701 baseEnd_3808701 := by
    simpa [prefixWord, tailWord_3808701, baseEnd_3808701] using wordTrace_append hprefix tailTrace_3808701
  have hstable : (prefixWord ++ tailWord_3808701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808701).length < 2 ^ (prefixWord ++ tailWord_3808701).sum := by decide
  have hdescent : baseEnd_3808701 < baseStart_3808701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808704 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_3808704 : Nat := 118140960795 + 3808704 * 2 ^ 59
def prefixEnd_3808704 : Nat := 4983230072969 + 3 ^ 40 * 3808704 * 2
def baseEnd_3808704 : Nat := 651898607567323887261365

theorem tailTrace_3808704 : CollatzResearch.WordTrace tailWord_3808704 prefixEnd_3808704 651898607567323887261365 := by
  unfold tailWord_3808704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69457423596861678850680583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92609898129148905134240777 69457423596861678850680583)
  ·
    refine ⟨104186135395292518276020875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69457423596861678850680583 104186135395292518276020875)
    ·
      refine ⟨156279203092938777414031313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104186135395292518276020875 156279203092938777414031313)
      ·
        refine ⟨117209402319704083060523485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156279203092938777414031313 117209402319704083060523485)
        ·
          refine ⟨43953525869889031147696307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117209402319704083060523485 43953525869889031147696307)
          ·
            refine ⟨65930288804833546721544461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43953525869889031147696307 65930288804833546721544461)
            ·
              refine ⟨24723858301812580020579173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65930288804833546721544461 24723858301812580020579173)
              ·
                refine ⟨4635723431589858753858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24723858301812580020579173 4635723431589858753858595)
                ·
                  refine ⟨6953585147384788130787893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635723431589858753858595 6953585147384788130787893)
                  ·
                    refine ⟨651898607567323887261365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6953585147384788130787893 651898607567323887261365)
                    ·
                      rfl

theorem cell23_3808704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_3808704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808704 prefixEnd_3808704 := by exact prefixLift 3808704
  have htrace : WordTrace (prefixWord ++ tailWord_3808704) baseStart_3808704 baseEnd_3808704 := by
    simpa [prefixWord, tailWord_3808704, baseEnd_3808704] using wordTrace_append hprefix tailTrace_3808704
  have hstable : (prefixWord ++ tailWord_3808704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808704).length < 2 ^ (prefixWord ++ tailWord_3808704).sum := by decide
  have hdescent : baseEnd_3808704 < baseStart_3808704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808711 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_3808711 : Nat := 118140960795 + 3808711 * 2 ^ 59
def prefixEnd_3808711 : Nat := 4983230072969 + 3 ^ 40 * 3808711 * 2
def baseEnd_3808711 : Nat := 1955699417066553134396563

theorem tailTrace_3808711 : CollatzResearch.WordTrace tailWord_3808711 prefixEnd_3808711 1955699417066553134396563 := by
  unfold tailWord_3808711
  simp only [CollatzResearch.WordTrace]
  refine ⟨138915102504697997896865987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92610068336465331931243991 138915102504697997896865987)
  ·
    refine ⟨208372653757046996845298981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138915102504697997896865987 208372653757046996845298981)
    ·
      refine ⟨39069872579446311908493559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208372653757046996845298981 39069872579446311908493559)
      ·
        refine ⟨58604808869169467862740339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39069872579446311908493559 58604808869169467862740339)
        ·
          refine ⟨87907213303754201794110509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58604808869169467862740339 87907213303754201794110509)
          ·
            refine ⟨32965204988907825672791441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87907213303754201794110509 32965204988907825672791441)
            ·
              refine ⟨24723903741680869254593581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32965204988907825672791441 24723903741680869254593581)
              ·
                refine ⟨9271463903130325970472593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24723903741680869254593581 9271463903130325970472593)
                ·
                  refine ⟨6953597927347744477854445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9271463903130325970472593 6953597927347744477854445)
                  ·
                    refine ⟨2607599222755404179195417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6953597927347744477854445 2607599222755404179195417)
                    ·
                      refine ⟨1955699417066553134396563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607599222755404179195417 1955699417066553134396563)
                      ·
                        rfl

theorem cell23_3808711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_3808711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808711 prefixEnd_3808711 := by exact prefixLift 3808711
  have htrace : WordTrace (prefixWord ++ tailWord_3808711) baseStart_3808711 baseEnd_3808711 := by
    simpa [prefixWord, tailWord_3808711, baseEnd_3808711] using wordTrace_append hprefix tailTrace_3808711
  have hstable : (prefixWord ++ tailWord_3808711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808711).length < 2 ^ (prefixWord ++ tailWord_3808711).sum := by decide
  have hdescent : baseEnd_3808711 < baseStart_3808711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808735 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 1, 1, 3]
def baseStart_3808735 : Nat := 118140960795 + 3808735 * 2 ^ 59
def prefixEnd_3808735 : Nat := 4983230072969 + 3 ^ 40 * 3808735 * 2
def baseEnd_3808735 : Nat := 1955711740602261040496453

theorem tailTrace_3808735 : CollatzResearch.WordTrace tailWord_3808735 prefixEnd_3808735 1955711740602261040496453 := by
  unfold tailWord_3808735
  simp only [CollatzResearch.WordTrace]
  refine ⟨138915977856611049995739659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92610651904407366663826439 138915977856611049995739659)
  ·
    refine ⟨208373966784916574993609489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138915977856611049995739659 208373966784916574993609489)
    ·
      refine ⟨156280475088687431245207117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208373966784916574993609489 156280475088687431245207117)
      ·
        refine ⟨58605178158257786716952669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156280475088687431245207117 58605178158257786716952669)
        ·
          refine ⟨21976941809346670018857251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58605178158257786716952669 21976941809346670018857251)
          ·
            refine ⟨32965412714020005028285877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21976941809346670018857251 32965412714020005028285877)
            ·
              refine ⟨3090507441939375471401801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32965412714020005028285877 3090507441939375471401801)
              ·
                refine ⟨2317880581454531603551351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090507441939375471401801 2317880581454531603551351)
                ·
                  refine ⟨3476820872181797405327027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317880581454531603551351 3476820872181797405327027)
                  ·
                    refine ⟨5215231308272696107990541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3476820872181797405327027 5215231308272696107990541)
                    ·
                      refine ⟨1955711740602261040496453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5215231308272696107990541 1955711740602261040496453)
                      ·
                        rfl

theorem cell23_3808735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_3808735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808735 prefixEnd_3808735 := by exact prefixLift 3808735
  have htrace : WordTrace (prefixWord ++ tailWord_3808735) baseStart_3808735 baseEnd_3808735 := by
    simpa [prefixWord, tailWord_3808735, baseEnd_3808735] using wordTrace_append hprefix tailTrace_3808735
  have hstable : (prefixWord ++ tailWord_3808735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808735).length < 2 ^ (prefixWord ++ tailWord_3808735).sum := by decide
  have hdescent : baseEnd_3808735 < baseStart_3808735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808744 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3808744 : Nat := 118140960795 + 3808744 * 2 ^ 59
def prefixEnd_3808744 : Nat := 4983230072969 + 3 ^ 40 * 3808744 * 2
def baseEnd_3808744 : Nat := 1955716361928151505283911

theorem tailTrace_3808744 : CollatzResearch.WordTrace tailWord_3808744 prefixEnd_3808744 1955716361928151505283911 := by
  unfold tailWord_3808744
  simp only [CollatzResearch.WordTrace]
  refine ⟨69458153056789222266408643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92610870742385629688544857 69458153056789222266408643)
  ·
    refine ⟨104187229585183833399612965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69458153056789222266408643 104187229585183833399612965)
    ·
      refine ⟨19535105547221968762427431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104187229585183833399612965 19535105547221968762427431)
      ·
        refine ⟨29302658320832953143641147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535105547221968762427431 29302658320832953143641147)
        ·
          refine ⟨43953987481249429715461721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29302658320832953143641147 43953987481249429715461721)
          ·
            refine ⟨32965490610937072286596291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43953987481249429715461721 32965490610937072286596291)
            ·
              refine ⟨49448235916405608429894437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32965490610937072286596291 49448235916405608429894437)
              ·
                refine ⟨9271544234326051580605207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49448235916405608429894437 9271544234326051580605207)
                ·
                  refine ⟨13907316351489077370907811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271544234326051580605207 13907316351489077370907811)
                  ·
                    refine ⟨20860974527233616056361717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13907316351489077370907811 20860974527233616056361717)
                    ·
                      refine ⟨1955716361928151505283911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20860974527233616056361717 1955716361928151505283911)
                      ·
                        rfl

theorem cell23_3808744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3808744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808744 prefixEnd_3808744 := by exact prefixLift 3808744
  have htrace : WordTrace (prefixWord ++ tailWord_3808744) baseStart_3808744 baseEnd_3808744 := by
    simpa [prefixWord, tailWord_3808744, baseEnd_3808744] using wordTrace_append hprefix tailTrace_3808744
  have hstable : (prefixWord ++ tailWord_3808744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808744).length < 2 ^ (prefixWord ++ tailWord_3808744).sum := by decide
  have hdescent : baseEnd_3808744 < baseStart_3808744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808758 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3808758 : Nat := 118140960795 + 3808758 * 2 ^ 59
def prefixEnd_3808758 : Nat := 4983230072969 + 3 ^ 40 * 3808758 * 2
def baseEnd_3808758 : Nat := 1955723550657314450508847

theorem tailTrace_3808758 : CollatzResearch.WordTrace tailWord_3808758 prefixEnd_3808758 1955723550657314450508847 := by
  unfold tailWord_3808758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682301045970482807739183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92611211157018483282551285 8682301045970482807739183)
  ·
    refine ⟨13023451568955724211608775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8682301045970482807739183 13023451568955724211608775)
    ·
      refine ⟨19535177353433586317413163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023451568955724211608775 19535177353433586317413163)
      ·
        refine ⟨29302766030150379476119745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535177353433586317413163 29302766030150379476119745)
        ·
          refine ⟨21977074522612784607089809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29302766030150379476119745 21977074522612784607089809)
          ·
            refine ⟨16482805891959588455317357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21977074522612784607089809 16482805891959588455317357)
            ·
              refine ⟨6181052209484845670744009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16482805891959588455317357 6181052209484845670744009)
              ·
                refine ⟨4635789157113634253058007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181052209484845670744009 4635789157113634253058007)
                ·
                  refine ⟨6953683735670451379587011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635789157113634253058007 6953683735670451379587011)
                  ·
                    refine ⟨10430525603505677069380517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6953683735670451379587011 10430525603505677069380517)
                    ·
                      refine ⟨1955723550657314450508847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10430525603505677069380517 1955723550657314450508847)
                      ·
                        rfl

theorem cell23_3808758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3808758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808758 prefixEnd_3808758 := by exact prefixLift 3808758
  have htrace : WordTrace (prefixWord ++ tailWord_3808758) baseStart_3808758 baseEnd_3808758 := by
    simpa [prefixWord, tailWord_3808758, baseEnd_3808758] using wordTrace_append hprefix tailTrace_3808758
  have hstable : (prefixWord ++ tailWord_3808758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808758).length < 2 ^ (prefixWord ++ tailWord_3808758).sum := by decide
  have hdescent : baseEnd_3808758 < baseStart_3808758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808781 : List Nat := [1, 7, 1, 1, 13]
def baseStart_3808781 : Nat := 118140960795 + 3808781 * 2 ^ 59
def prefixEnd_3808781 : Nat := 4983230072969 + 3 ^ 40 * 3808781 * 2
def baseEnd_3808781 : Nat := 2682764555160998436929

theorem tailTrace_3808781 : CollatzResearch.WordTrace tailWord_3808781 prefixEnd_3808781 2682764555160998436929 := by
  unfold tailWord_3808781
  simp only [CollatzResearch.WordTrace]
  refine ⟨138917655614444399851914197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92611770409629599901276131 138917655614444399851914197)
  ·
    refine ⟨3255882553463540621529239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 138917655614444399851914197 3255882553463540621529239)
    ·
      refine ⟨4883823830195310932293859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3255882553463540621529239 4883823830195310932293859)
      ·
        refine ⟨7325735745292966398440789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883823830195310932293859 7325735745292966398440789)
        ·
          refine ⟨2682764555160998436929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7325735745292966398440789 2682764555160998436929)
          ·
            rfl

theorem cell23_3808781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 13].length) (baseStart_3808781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808781 prefixEnd_3808781 := by exact prefixLift 3808781
  have htrace : WordTrace (prefixWord ++ tailWord_3808781) baseStart_3808781 baseEnd_3808781 := by
    simpa [prefixWord, tailWord_3808781, baseEnd_3808781] using wordTrace_append hprefix tailTrace_3808781
  have hstable : (prefixWord ++ tailWord_3808781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808781).length < 2 ^ (prefixWord ++ tailWord_3808781).sum := by decide
  have hdescent : baseEnd_3808781 < baseStart_3808781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808792 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 1, 2, 2]
def baseStart_3808792 : Nat := 118140960795 + 3808792 * 2 ^ 59
def prefixEnd_3808792 : Nat := 4983230072969 + 3 ^ 40 * 3808792 * 2
def baseEnd_3808792 : Nat := 1955741008999567317483691

theorem tailTrace_3808792 : CollatzResearch.WordTrace tailWord_3808792 prefixEnd_3808792 1955741008999567317483691 := by
  unfold tailWord_3808792
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459028408702274365282315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92612037878269699153709753 69459028408702274365282315)
  ·
    refine ⟨104188542613053411547923473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69459028408702274365282315 104188542613053411547923473)
    ·
      refine ⟨78141406959790058660942605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104188542613053411547923473 78141406959790058660942605)
      ·
        refine ⟨29303027609921271997853477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78141406959790058660942605 29303027609921271997853477)
        ·
          refine ⟨5494317676860238499597527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29303027609921271997853477 5494317676860238499597527)
          ·
            refine ⟨8241476515290357749396291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494317676860238499597527 8241476515290357749396291)
            ·
              refine ⟨12362214772935536624094437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241476515290357749396291 12362214772935536624094437)
              ·
                refine ⟨2317915269925413117017707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12362214772935536624094437 2317915269925413117017707)
                ·
                  refine ⟨3476872904888119675526561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317915269925413117017707 3476872904888119675526561)
                  ·
                    refine ⟨2607654678666089756644921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476872904888119675526561 2607654678666089756644921)
                    ·
                      refine ⟨1955741008999567317483691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607654678666089756644921 1955741008999567317483691)
                      ·
                        rfl

theorem cell23_3808792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_3808792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808792 prefixEnd_3808792 := by exact prefixLift 3808792
  have htrace : WordTrace (prefixWord ++ tailWord_3808792) baseStart_3808792 baseEnd_3808792 := by
    simpa [prefixWord, tailWord_3808792, baseEnd_3808792] using wordTrace_append hprefix tailTrace_3808792
  have hstable : (prefixWord ++ tailWord_3808792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808792).length < 2 ^ (prefixWord ++ tailWord_3808792).sum := by decide
  have hdescent : baseEnd_3808792 < baseStart_3808792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808818 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_3808818 : Nat := 118140960795 + 3808818 * 2 ^ 59
def prefixEnd_3808818 : Nat := 4983230072969 + 3 ^ 40 * 3808818 * 2
def baseEnd_3808818 : Nat := 1955754359496584215758571

theorem tailTrace_3808818 : CollatzResearch.WordTrace tailWord_3808818 prefixEnd_3808818 1955754359496584215758571 := by
  unfold tailWord_3808818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729751278827588792752777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92612670076873570114007405 34729751278827588792752777)
  ·
    refine ⟨26047313459120691594564583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34729751278827588792752777 26047313459120691594564583)
    ·
      refine ⟨39070970188681037391846875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047313459120691594564583 39070970188681037391846875)
      ·
        refine ⟨58606455283021556087770313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39070970188681037391846875 58606455283021556087770313)
        ·
          refine ⟨43954841462266167065827735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58606455283021556087770313 43954841462266167065827735)
          ·
            refine ⟨65932262193399250598741603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43954841462266167065827735 65932262193399250598741603)
            ·
              refine ⟨98898393290098875898112405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65932262193399250598741603 98898393290098875898112405)
              ·
                refine ⟨4635862185473384807724019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98898393290098875898112405 4635862185473384807724019)
                ·
                  refine ⟨6953793278210077211586029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4635862185473384807724019 6953793278210077211586029)
                  ·
                    refine ⟨2607672479328778954344761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6953793278210077211586029 2607672479328778954344761)
                    ·
                      refine ⟨1955754359496584215758571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607672479328778954344761 1955754359496584215758571)
                      ·
                        rfl

theorem cell23_3808818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_3808818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808818 prefixEnd_3808818 := by exact prefixLift 3808818
  have htrace : WordTrace (prefixWord ++ tailWord_3808818) baseStart_3808818 baseEnd_3808818 := by
    simpa [prefixWord, tailWord_3808818, baseEnd_3808818] using wordTrace_append hprefix tailTrace_3808818
  have hstable : (prefixWord ++ tailWord_3808818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808818).length < 2 ^ (prefixWord ++ tailWord_3808818).sum := by decide
  have hdescent : baseEnd_3808818 < baseStart_3808818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808848 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2]
def baseStart_3808848 : Nat := 118140960795 + 3808848 * 2 ^ 59
def prefixEnd_3808848 : Nat := 4983230072969 + 3 ^ 40 * 3808848 * 2
def baseEnd_3808848 : Nat := 1955769763916219098383433

theorem tailTrace_3808848 : CollatzResearch.WordTrace tailWord_3808848 prefixEnd_3808848 1955769763916219098383433 := by
  unfold tailWord_3808848
  simp only [CollatzResearch.WordTrace]
  refine ⟨69460049652600835147301599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92613399536801113529735465 69460049652600835147301599)
  ·
    refine ⟨104190074478901252720952399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69460049652600835147301599 104190074478901252720952399)
    ·
      refine ⟨156285111718351879081428599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104190074478901252720952399 156285111718351879081428599)
      ·
        refine ⟨234427667577527818622142899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156285111718351879081428599 234427667577527818622142899)
        ·
          refine ⟨351641501366291727933214349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234427667577527818622142899 351641501366291727933214349)
          ·
            refine ⟨131865563012359397974955381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351641501366291727933214349 131865563012359397974955381)
            ·
              refine ⟨12362396532408693560152067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131865563012359397974955381 12362396532408693560152067)
              ·
                refine ⟨18543594798613040340228101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362396532408693560152067 18543594798613040340228101)
                ·
                  refine ⟨3476924024739945063792769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18543594798613040340228101 3476924024739945063792769)
                  ·
                    refine ⟨2607693018554958797844577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476924024739945063792769 2607693018554958797844577)
                    ·
                      refine ⟨1955769763916219098383433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607693018554958797844577 1955769763916219098383433)
                      ·
                        rfl

theorem cell23_3808848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2].length) (baseStart_3808848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808848 prefixEnd_3808848 := by exact prefixLift 3808848
  have htrace : WordTrace (prefixWord ++ tailWord_3808848) baseStart_3808848 baseEnd_3808848 := by
    simpa [prefixWord, tailWord_3808848, baseEnd_3808848] using wordTrace_append hprefix tailTrace_3808848
  have hstable : (prefixWord ++ tailWord_3808848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808848).length < 2 ^ (prefixWord ++ tailWord_3808848).sum := by decide
  have hdescent : baseEnd_3808848 < baseStart_3808848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808901 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3808901 : Nat := 118140960795 + 3808901 * 2 ^ 59
def prefixEnd_3808901 : Nat := 4983230072969 + 3 ^ 40 * 3808901 * 2
def baseEnd_3808901 : Nat := 651932326130302463673563

theorem tailTrace_3808901 : CollatzResearch.WordTrace tailWord_3808901 prefixEnd_3808901 651932326130302463673563 := by
  unfold tailWord_3808901
  simp only [CollatzResearch.WordTrace]
  refine ⟨138922032374009660346282557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92614688249339773564188371 138922032374009660346282557)
  ·
    refine ⟨52095762140253622629855959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138922032374009660346282557 52095762140253622629855959)
    ·
      refine ⟨78143643210380433944783939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52095762140253622629855959 78143643210380433944783939)
      ·
        refine ⟨117215464815570650917175909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78143643210380433944783939 117215464815570650917175909)
        ·
          refine ⟨21977899652919497046970483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117215464815570650917175909 21977899652919497046970483)
          ·
            refine ⟨32966849479379245570455725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21977899652919497046970483 32966849479379245570455725)
            ·
              refine ⟨12362568554767217088920897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32966849479379245570455725 12362568554767217088920897)
              ·
                refine ⟨9271926416075412816690673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12362568554767217088920897 9271926416075412816690673)
                ·
                  refine ⟨6953944812056559612518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9271926416075412816690673 6953944812056559612518005)
                  ·
                    refine ⟨651932326130302463673563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6953944812056559612518005 651932326130302463673563)
                    ·
                      rfl

theorem cell23_3808901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3808901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808901 prefixEnd_3808901 := by exact prefixLift 3808901
  have htrace : WordTrace (prefixWord ++ tailWord_3808901) baseStart_3808901 baseEnd_3808901 := by
    simpa [prefixWord, tailWord_3808901, baseEnd_3808901] using wordTrace_append hprefix tailTrace_3808901
  have hstable : (prefixWord ++ tailWord_3808901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808901).length < 2 ^ (prefixWord ++ tailWord_3808901).sum := by decide
  have hdescent : baseEnd_3808901 < baseStart_3808901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808916 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3808916 : Nat := 118140960795 + 3808916 * 2 ^ 59
def prefixEnd_3808916 : Nat := 4983230072969 + 3 ^ 40 * 3808916 * 2
def baseEnd_3808916 : Nat := 1955804680600724832333121

theorem tailTrace_3808916 : CollatzResearch.WordTrace tailWord_3808916 prefixEnd_3808916 1955804680600724832333121 := by
  unfold tailWord_3808916
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461289734477658954039301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92615052979303545272052401 69461289734477658954039301)
  ·
    refine ⟨13023991825214561053882369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69461289734477658954039301 13023991825214561053882369)
    ·
      refine ⟨9767993868910920790411777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13023991825214561053882369 9767993868910920790411777)
      ·
        refine ⟨7325995401683190592808833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9767993868910920790411777 7325995401683190592808833)
        ·
          refine ⟨5494496551262392944606625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7325995401683190592808833 5494496551262392944606625)
          ·
            refine ⟨4120872413446794708454969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494496551262392944606625 4120872413446794708454969)
            ·
              refine ⟨3090654310085096031341227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120872413446794708454969 3090654310085096031341227)
              ·
                refine ⟨4635981465127644047011841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090654310085096031341227 4635981465127644047011841)
                ·
                  refine ⟨3476986098845733035258881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635981465127644047011841 3476986098845733035258881)
                  ·
                    refine ⟨2607739574134299776444161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3476986098845733035258881 2607739574134299776444161)
                    ·
                      refine ⟨1955804680600724832333121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607739574134299776444161 1955804680600724832333121)
                      ·
                        rfl

theorem cell23_3808916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3808916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808916 prefixEnd_3808916 := by exact prefixLift 3808916
  have htrace : WordTrace (prefixWord ++ tailWord_3808916) baseStart_3808916 baseEnd_3808916 := by
    simpa [prefixWord, tailWord_3808916, baseEnd_3808916] using wordTrace_append hprefix tailTrace_3808916
  have hstable : (prefixWord ++ tailWord_3808916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808916).length < 2 ^ (prefixWord ++ tailWord_3808916).sum := by decide
  have hdescent : baseEnd_3808916 < baseStart_3808916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808931 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 5, 4]
def baseStart_3808931 : Nat := 118140960795 + 3808931 * 2 ^ 59
def prefixEnd_3808931 : Nat := 4983230072969 + 3 ^ 40 * 3808931 * 2
def baseEnd_3808931 : Nat := 651937460936847424548517

theorem tailTrace_3808931 : CollatzResearch.WordTrace tailWord_3808931 prefixEnd_3808931 651937460936847424548517 := by
  unfold tailWord_3808931
  simp only [CollatzResearch.WordTrace]
  refine ⟨138923126563900975469874647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92615417709267316979916431 138923126563900975469874647)
  ·
    refine ⟨208384689845851463204811971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138923126563900975469874647 208384689845851463204811971)
    ·
      refine ⟨312577034768777194807217957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208384689845851463204811971 312577034768777194807217957)
      ·
        refine ⟨58608194019145724026353367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312577034768777194807217957 58608194019145724026353367)
        ·
          refine ⟨87912291028718586039530051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58608194019145724026353367 87912291028718586039530051)
          ·
            refine ⟨131868436543077879059295077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87912291028718586039530051 131868436543077879059295077)
            ·
              refine ⟨24725331851827102323617827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131868436543077879059295077 24725331851827102323617827)
              ·
                refine ⟨37087997777740653485426741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24725331851827102323617827 37087997777740653485426741)
                ·
                  refine ⟨3476999791663186264258757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37087997777740653485426741 3476999791663186264258757)
                  ·
                    refine ⟨651937460936847424548517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3476999791663186264258757 651937460936847424548517)
                    ·
                      rfl

theorem cell23_3808931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 4].length) (baseStart_3808931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808931 prefixEnd_3808931 := by exact prefixLift 3808931
  have htrace : WordTrace (prefixWord ++ tailWord_3808931) baseStart_3808931 baseEnd_3808931 := by
    simpa [prefixWord, tailWord_3808931, baseEnd_3808931] using wordTrace_append hprefix tailTrace_3808931
  have hstable : (prefixWord ++ tailWord_3808931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808931).length < 2 ^ (prefixWord ++ tailWord_3808931).sum := by decide
  have hdescent : baseEnd_3808931 < baseStart_3808931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808944 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 10]
def baseStart_3808944 : Nat := 118140960795 + 3808944 * 2 ^ 59
def prefixEnd_3808944 : Nat := 4983230072969 + 3 ^ 40 * 3808944 * 2
def baseEnd_3808944 : Nat := 217313228673227858086999

theorem tailTrace_3808944 : CollatzResearch.WordTrace tailWord_3808944 prefixEnd_3808944 217313228673227858086999 := by
  unfold tailWord_3808944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461800356426939345048943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92615733808569252460065257 69461800356426939345048943)
  ·
    refine ⟨104192700534640409017573415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69461800356426939345048943 104192700534640409017573415)
    ·
      refine ⟨156289050801960613526360123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104192700534640409017573415 156289050801960613526360123)
      ·
        refine ⟨234433576202940920289540185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156289050801960613526360123 234433576202940920289540185)
        ·
          refine ⟨175825182152205690217155139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234433576202940920289540185 175825182152205690217155139)
          ·
            refine ⟨263737773228308535325732709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175825182152205690217155139 263737773228308535325732709)
            ·
              refine ⟨49450832480307850373574883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263737773228308535325732709 49450832480307850373574883)
              ·
                refine ⟨74176248720461775560362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49450832480307850373574883 74176248720461775560362325)
                ·
                  refine ⟨217313228673227858086999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74176248720461775560362325 217313228673227858086999)
                  ·
                    rfl

theorem cell23_3808944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_3808944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808944 prefixEnd_3808944 := by exact prefixLift 3808944
  have htrace : WordTrace (prefixWord ++ tailWord_3808944) baseStart_3808944 baseEnd_3808944 := by
    simpa [prefixWord, tailWord_3808944, baseEnd_3808944] using wordTrace_append hprefix tailTrace_3808944
  have hstable : (prefixWord ++ tailWord_3808944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808944).length < 2 ^ (prefixWord ++ tailWord_3808944).sum := by decide
  have hdescent : baseEnd_3808944 < baseStart_3808944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808978 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3808978 : Nat := 118140960795 + 3808978 * 2 ^ 59
def prefixEnd_3808978 : Nat := 4983230072969 + 3 ^ 40 * 3808978 * 2
def baseEnd_3808978 : Nat := 217315168489033732195315

theorem tailTrace_3808978 : CollatzResearch.WordTrace tailWord_3808978 prefixEnd_3808978 217315168489033732195315 := by
  unfold tailWord_3808978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731210198682675624208897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92616560529820468331223725 34731210198682675624208897)
  ·
    refine ⟨26048407649012006718156673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34731210198682675624208897 26048407649012006718156673)
    ·
      refine ⟨19536305736759005038617505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26048407649012006718156673 19536305736759005038617505)
      ·
        refine ⟨14652229302569253778963129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19536305736759005038617505 14652229302569253778963129)
        ·
          refine ⟨10989171976926940334222347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14652229302569253778963129 10989171976926940334222347)
          ·
            refine ⟨16483757965390410501333521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989171976926940334222347 16483757965390410501333521)
            ·
              refine ⟨12362818474042807876000141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16483757965390410501333521 12362818474042807876000141)
              ·
                refine ⟨4636056927766052953500053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12362818474042807876000141 4636056927766052953500053)
                ·
                  refine ⟨217315168489033732195315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4636056927766052953500053 217315168489033732195315)
                  ·
                    rfl

theorem cell23_3808978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3808978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808978 prefixEnd_3808978 := by exact prefixLift 3808978
  have htrace : WordTrace (prefixWord ++ tailWord_3808978) baseStart_3808978 baseEnd_3808978 := by
    simpa [prefixWord, tailWord_3808978, baseEnd_3808978] using wordTrace_append hprefix tailTrace_3808978
  have hstable : (prefixWord ++ tailWord_3808978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808978).length < 2 ^ (prefixWord ++ tailWord_3808978).sum := by decide
  have hdescent : baseEnd_3808978 < baseStart_3808978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808989 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3808989 : Nat := 118140960795 + 3808989 * 2 ^ 59
def prefixEnd_3808989 : Nat := 4983230072969 + 3 ^ 40 * 3808989 * 2
def baseEnd_3808989 : Nat := 1955842164688503046720285

theorem tailTrace_3808989 : CollatzResearch.WordTrace tailWord_3808989 prefixEnd_3808989 1955842164688503046720285 := by
  unfold tailWord_3808989
  simp only [CollatzResearch.WordTrace]
  refine ⟨138925241997690851375486021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92616827998460567583657347 138925241997690851375486021)
  ·
    refine ⟨26048482874567034632903629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138925241997690851375486021 26048482874567034632903629)
    ·
      refine ⟨9768181077962637987338861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26048482874567034632903629 9768181077962637987338861)
      ·
        refine ⟨3663067904235989245252073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9768181077962637987338861 3663067904235989245252073)
        ·
          refine ⟨2747300928176991933939055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663067904235989245252073 2747300928176991933939055)
          ·
            refine ⟨4120951392265487900908583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747300928176991933939055 4120951392265487900908583)
            ·
              refine ⟨6181427088398231851362875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120951392265487900908583 6181427088398231851362875)
              ·
                refine ⟨9272140632597347777044313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181427088398231851362875 9272140632597347777044313)
                ·
                  refine ⟨6954105474448010832783235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272140632597347777044313 6954105474448010832783235)
                  ·
                    refine ⟨10431158211672016249174853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954105474448010832783235 10431158211672016249174853)
                    ·
                      refine ⟨1955842164688503046720285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10431158211672016249174853 1955842164688503046720285)
                      ·
                        rfl

theorem cell23_3808989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3808989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808989 prefixEnd_3808989 := by exact prefixLift 3808989
  have htrace : WordTrace (prefixWord ++ tailWord_3808989) baseStart_3808989 baseEnd_3808989 := by
    simpa [prefixWord, tailWord_3808989, baseEnd_3808989] using wordTrace_append hprefix tailTrace_3808989
  have hstable : (prefixWord ++ tailWord_3808989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808989).length < 2 ^ (prefixWord ++ tailWord_3808989).sum := by decide
  have hdescent : baseEnd_3808989 < baseStart_3808989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808991 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 3, 5]
def baseStart_3808991 : Nat := 118140960795 + 3808991 * 2 ^ 59
def prefixEnd_3808991 : Nat := 4983230072969 + 3 ^ 40 * 3808991 * 2
def baseEnd_3808991 : Nat := 651947730549937346298425

theorem tailTrace_3808991 : CollatzResearch.WordTrace tailWord_3808991 prefixEnd_3808991 651947730549937346298425 := by
  unfold tailWord_3808991
  simp only [CollatzResearch.WordTrace]
  refine ⟨138925314943683605717058827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92616876629122403811372551 138925314943683605717058827)
  ·
    refine ⟨208387972415525408575588241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138925314943683605717058827 208387972415525408575588241)
    ·
      refine ⟨156290979311644056431691181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208387972415525408575588241 156290979311644056431691181)
      ·
        refine ⟨58609117241866521161884193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156290979311644056431691181 58609117241866521161884193)
        ·
          refine ⟨43956837931399890871413145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58609117241866521161884193 43956837931399890871413145)
          ·
            refine ⟨32967628448549918153559859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43956837931399890871413145 32967628448549918153559859)
            ·
              refine ⟨49451442672824877230339789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32967628448549918153559859 49451442672824877230339789)
              ·
                refine ⟨18544291002309328961377421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49451442672824877230339789 18544291002309328961377421)
                ·
                  refine ⟨6954109125865998360516533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18544291002309328961377421 6954109125865998360516533)
                  ·
                    refine ⟨651947730549937346298425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6954109125865998360516533 651947730549937346298425)
                    ·
                      rfl

theorem cell23_3808991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_3808991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808991 prefixEnd_3808991 := by exact prefixLift 3808991
  have htrace : WordTrace (prefixWord ++ tailWord_3808991) baseStart_3808991 baseEnd_3808991 := by
    simpa [prefixWord, tailWord_3808991, baseEnd_3808991] using wordTrace_append hprefix tailTrace_3808991
  have hstable : (prefixWord ++ tailWord_3808991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808991).length < 2 ^ (prefixWord ++ tailWord_3808991).sum := by decide
  have hdescent : baseEnd_3808991 < baseStart_3808991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808999 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3808999 : Nat := 118140960795 + 3808999 * 2 ^ 59
def prefixEnd_3808999 : Nat := 4983230072969 + 3 ^ 40 * 3808999 * 2
def baseEnd_3808999 : Nat := 651949099831682669198413

theorem tailTrace_3808999 : CollatzResearch.WordTrace tailWord_3808999 prefixEnd_3808999 651949099831682669198413 := by
  unfold tailWord_3808999
  simp only [CollatzResearch.WordTrace]
  refine ⟨138925606727654623083350051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92617071151769748722233367 138925606727654623083350051)
  ·
    refine ⟨208388410091481934625025077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138925606727654623083350051 208388410091481934625025077)
    ·
      refine ⟨19536413446076431371096101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208388410091481934625025077 19536413446076431371096101)
      ·
        refine ⟨3663077521139330882080519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19536413446076431371096101 3663077521139330882080519)
        ·
          refine ⟨5494616281708996323120779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663077521139330882080519 5494616281708996323120779)
          ·
            refine ⟨8241924422563494484681169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494616281708996323120779 8241924422563494484681169)
            ·
              refine ⟨6181443316922620863510877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241924422563494484681169 6181443316922620863510877)
              ·
                refine ⟨2318041243845982823816579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6181443316922620863510877 2318041243845982823816579)
                ·
                  refine ⟨3477061865768974235724869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318041243845982823816579 3477061865768974235724869)
                  ·
                    refine ⟨651949099831682669198413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477061865768974235724869 651949099831682669198413)
                    ·
                      rfl

theorem cell23_3808999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3808999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3808999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3808999 prefixEnd_3808999 := by exact prefixLift 3808999
  have htrace : WordTrace (prefixWord ++ tailWord_3808999) baseStart_3808999 baseEnd_3808999 := by
    simpa [prefixWord, tailWord_3808999, baseEnd_3808999] using wordTrace_append hprefix tailTrace_3808999
  have hstable : (prefixWord ++ tailWord_3808999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808999).length < 2 ^ (prefixWord ++ tailWord_3808999).sum := by decide
  have hdescent : baseEnd_3808999 < baseStart_3808999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809012 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3809012 : Nat := 118140960795 + 3809012 * 2 ^ 59
def prefixEnd_3809012 : Nat := 4983230072969 + 3 ^ 40 * 3809012 * 2
def baseEnd_3809012 : Nat := 217317108304839606303631

theorem tailTrace_3809012 : CollatzResearch.WordTrace tailWord_3809012 prefixEnd_3809012 217317108304839606303631 := by
  unfold tailWord_3809012
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463040438303763151786645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92617387251071684202382193 69463040438303763151786645)
  ·
    refine ⟨3256080020545488897739999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69463040438303763151786645 3256080020545488897739999)
    ·
      refine ⟨4884120030818233346609999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256080020545488897739999 4884120030818233346609999)
      ·
        refine ⟨7326180046227350019914999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884120030818233346609999 7326180046227350019914999)
        ·
          refine ⟨10989270069341025029872499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326180046227350019914999 10989270069341025029872499)
          ·
            refine ⟨16483905104011537544808749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989270069341025029872499 16483905104011537544808749)
            ·
              refine ⟨6181464414004326579303281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16483905104011537544808749 6181464414004326579303281)
              ·
                refine ⟨4636098310503244934477461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181464414004326579303281 4636098310503244934477461)
                ·
                  refine ⟨217317108304839606303631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4636098310503244934477461 217317108304839606303631)
                  ·
                    rfl

theorem cell23_3809012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3809012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809012 prefixEnd_3809012 := by exact prefixLift 3809012
  have htrace : WordTrace (prefixWord ++ tailWord_3809012) baseStart_3809012 baseEnd_3809012 := by
    simpa [prefixWord, tailWord_3809012, baseEnd_3809012] using wordTrace_append hprefix tailTrace_3809012
  have hstable : (prefixWord ++ tailWord_3809012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809012).length < 2 ^ (prefixWord ++ tailWord_3809012).sum := by decide
  have hdescent : baseEnd_3809012 < baseStart_3809012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809038 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_3809038 : Nat := 118140960795 + 3809038 * 2 ^ 59
def prefixEnd_3809038 : Nat := 4983230072969 + 3 ^ 40 * 3809038 * 2
def baseEnd_3809038 : Nat := 651955775080191118335853

theorem tailTrace_3809038 : CollatzResearch.WordTrace tailWord_3809038 prefixEnd_3809038 651955775080191118335853 := by
  unfold tailWord_3809038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365878646814166593002471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92618019449675555162679845 17365878646814166593002471)
  ·
    refine ⟨26048817970221249889503707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17365878646814166593002471 26048817970221249889503707)
    ·
      refine ⟨39073226955331874834255561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26048817970221249889503707 39073226955331874834255561)
      ·
        refine ⟨29304920216498906125691671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39073226955331874834255561 29304920216498906125691671)
        ·
          refine ⟨43957380324748359188537507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29304920216498906125691671 43957380324748359188537507)
          ·
            refine ⟨65936070487122538782806261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43957380324748359188537507 65936070487122538782806261)
            ·
              refine ⟨6181506608167738010888087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65936070487122538782806261 6181506608167738010888087)
              ·
                refine ⟨9272259912251607016332131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181506608167738010888087 9272259912251607016332131)
                ·
                  refine ⟨13908389868377410524498197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272259912251607016332131 13908389868377410524498197)
                  ·
                    refine ⟨651955775080191118335853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13908389868377410524498197 651955775080191118335853)
                    ·
                      rfl

theorem cell23_3809038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_3809038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809038 prefixEnd_3809038 := by exact prefixLift 3809038
  have htrace : WordTrace (prefixWord ++ tailWord_3809038) baseStart_3809038 baseEnd_3809038 := by
    simpa [prefixWord, tailWord_3809038, baseEnd_3809038] using wordTrace_append hprefix tailTrace_3809038
  have hstable : (prefixWord ++ tailWord_3809038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809038).length < 2 ^ (prefixWord ++ tailWord_3809038).sum := by decide
  have hdescent : baseEnd_3809038 < baseStart_3809038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809042 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3809042 : Nat := 118140960795 + 3809042 * 2 ^ 59
def prefixEnd_3809042 : Nat := 4983230072969 + 3 ^ 40 * 3809042 * 2
def baseEnd_3809042 : Nat := 651956459721063779785847

theorem tailTrace_3809042 : CollatzResearch.WordTrace tailWord_3809042 prefixEnd_3809042 651956459721063779785847 := by
  unfold tailWord_3809042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731793766624710356791345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92618116710999227618110253 34731793766624710356791345)
  ·
    refine ⟨26048845324968532767593509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34731793766624710356791345 26048845324968532767593509)
    ·
      refine ⟨4884158498431599893923783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26048845324968532767593509 4884158498431599893923783)
      ·
        refine ⟨7326237747647399840885675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884158498431599893923783 7326237747647399840885675)
        ·
          refine ⟨10989356621471099761328513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326237747647399840885675 10989356621471099761328513)
          ·
            refine ⟨8242017466103324820996385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10989356621471099761328513 8242017466103324820996385)
            ·
              refine ⟨6181513099577493615747289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242017466103324820996385 6181513099577493615747289)
              ·
                refine ⟨4636134824683120211810467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181513099577493615747289 4636134824683120211810467)
                ·
                  refine ⟨6954202237024680317715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636134824683120211810467 6954202237024680317715701)
                  ·
                    refine ⟨651956459721063779785847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6954202237024680317715701 651956459721063779785847)
                    ·
                      rfl

theorem cell23_3809042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3809042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809042 prefixEnd_3809042 := by exact prefixLift 3809042
  have htrace : WordTrace (prefixWord ++ tailWord_3809042) baseStart_3809042 baseEnd_3809042 := by
    simpa [prefixWord, tailWord_3809042, baseEnd_3809042] using wordTrace_append hprefix tailTrace_3809042
  have hstable : (prefixWord ++ tailWord_3809042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809042).length < 2 ^ (prefixWord ++ tailWord_3809042).sum := by decide
  have hdescent : baseEnd_3809042 < baseStart_3809042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809045 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3809045 : Nat := 118140960795 + 3809045 * 2 ^ 59
def prefixEnd_3809045 : Nat := 4983230072969 + 3 ^ 40 * 3809045 * 2
def baseEnd_3809045 : Nat := 1955870919605154827620027

theorem tailTrace_3809045 : CollatzResearch.WordTrace tailWord_3809045 prefixEnd_3809045 1955870919605154827620027 := by
  unfold tailWord_3809045
  simp only [CollatzResearch.WordTrace]
  refine ⟨138927284485487972939524589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92618189656991981959683059 138927284485487972939524589)
  ·
    refine ⟨52097731682057989852321721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138927284485487972939524589 52097731682057989852321721)
    ·
      refine ⟨39073298761543492389241291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52097731682057989852321721 39073298761543492389241291)
      ·
        refine ⟨58609948142315238583861937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39073298761543492389241291 58609948142315238583861937)
        ·
          refine ⟨43957461106736428937896453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58609948142315238583861937 43957461106736428937896453)
          ·
            refine ⟨8242023957513080425855585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43957461106736428937896453 8242023957513080425855585)
            ·
              refine ⟨6181517968134810319391689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242023957513080425855585 6181517968134810319391689)
              ·
                refine ⟨4636138476101107739543767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181517968134810319391689 4636138476101107739543767)
                ·
                  refine ⟨6954207714151661609315651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636138476101107739543767 6954207714151661609315651)
                  ·
                    refine ⟨10431311571227492413973477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954207714151661609315651 10431311571227492413973477)
                    ·
                      refine ⟨1955870919605154827620027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10431311571227492413973477 1955870919605154827620027)
                      ·
                        rfl

theorem cell23_3809045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3809045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809045 prefixEnd_3809045 := by exact prefixLift 3809045
  have htrace : WordTrace (prefixWord ++ tailWord_3809045) baseStart_3809045 baseEnd_3809045 := by
    simpa [prefixWord, tailWord_3809045, baseEnd_3809045] using wordTrace_append hprefix tailTrace_3809045
  have hstable : (prefixWord ++ tailWord_3809045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809045).length < 2 ^ (prefixWord ++ tailWord_3809045).sum := by decide
  have hdescent : baseEnd_3809045 < baseStart_3809045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809048 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3809048 : Nat := 118140960795 + 3809048 * 2 ^ 59
def prefixEnd_3809048 : Nat := 4983230072969 + 3 ^ 40 * 3809048 * 2
def baseEnd_3809048 : Nat := 1955872460047118315882513

theorem tailTrace_3809048 : CollatzResearch.WordTrace tailWord_3809048 prefixEnd_3809048 1955872460047118315882513 := by
  unfold tailWord_3809048
  simp only [CollatzResearch.WordTrace]
  refine ⟨69463696952238552225941899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92618262602984736301255865 69463696952238552225941899)
  ·
    refine ⟨104195545428357828338912849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69463696952238552225941899 104195545428357828338912849)
    ·
      refine ⟨78146659071268371254184637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104195545428357828338912849 78146659071268371254184637)
      ·
        refine ⟨29304997151725639220319239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78146659071268371254184637 29304997151725639220319239)
        ·
          refine ⟨43957495727588458830478859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29304997151725639220319239 43957495727588458830478859)
          ·
            refine ⟨65936243591382688245718289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43957495727588458830478859 65936243591382688245718289)
            ·
              refine ⟨49452182693537016184288717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65936243591382688245718289 49452182693537016184288717)
              ·
                refine ⟨18544568510076381069108269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49452182693537016184288717 18544568510076381069108269)
                ·
                  refine ⟨6954213191278642900915601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18544568510076381069108269 6954213191278642900915601)
                  ·
                    refine ⟨5215659893458982175686701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954213191278642900915601 5215659893458982175686701)
                    ·
                      refine ⟨1955872460047118315882513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5215659893458982175686701 1955872460047118315882513)
                      ·
                        rfl

theorem cell23_3809048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3809048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809048 prefixEnd_3809048 := by exact prefixLift 3809048
  have htrace : WordTrace (prefixWord ++ tailWord_3809048) baseStart_3809048 baseEnd_3809048 := by
    simpa [prefixWord, tailWord_3809048, baseEnd_3809048] using wordTrace_append hprefix tailTrace_3809048
  have hstable : (prefixWord ++ tailWord_3809048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809048).length < 2 ^ (prefixWord ++ tailWord_3809048).sum := by decide
  have hdescent : baseEnd_3809048 < baseStart_3809048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809058 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3809058 : Nat := 118140960795 + 3809058 * 2 ^ 59
def prefixEnd_3809058 : Nat := 4983230072969 + 3 ^ 40 * 3809058 * 2
def baseEnd_3809058 : Nat := 1955877594853663276757467

theorem tailTrace_3809058 : CollatzResearch.WordTrace tailWord_3809058 prefixEnd_3809058 1955877594853663276757467 := by
  unfold tailWord_3809058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34731939658610219039936957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92618505756293917439831885 34731939658610219039936957)
  ·
    refine ⟨13024477371978832139976359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34731939658610219039936957 13024477371978832139976359)
    ·
      refine ⟨19536716057968248209964539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13024477371978832139976359 19536716057968248209964539)
      ·
        refine ⟨29305074086952372314946809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19536716057968248209964539 29305074086952372314946809)
        ·
          refine ⟨21978805565214279236210107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29305074086952372314946809 21978805565214279236210107)
          ·
            refine ⟨32968208347821418854315161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978805565214279236210107 32968208347821418854315161)
            ·
              refine ⟨24726156260866064140736371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32968208347821418854315161 24726156260866064140736371)
              ·
                refine ⟨37089234391299096211104557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24726156260866064140736371 37089234391299096211104557)
                ·
                  refine ⟨13908462896737161079164209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37089234391299096211104557 13908462896737161079164209)
                  ·
                    refine ⟨10431347172552870809373157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13908462896737161079164209 10431347172552870809373157)
                    ·
                      refine ⟨1955877594853663276757467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10431347172552870809373157 1955877594853663276757467)
                      ·
                        rfl

theorem cell23_3809058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3809058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809058 prefixEnd_3809058 := by exact prefixLift 3809058
  have htrace : WordTrace (prefixWord ++ tailWord_3809058) baseStart_3809058 baseEnd_3809058 := by
    simpa [prefixWord, tailWord_3809058, baseEnd_3809058] using wordTrace_append hprefix tailTrace_3809058
  have hstable : (prefixWord ++ tailWord_3809058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809058).length < 2 ^ (prefixWord ++ tailWord_3809058).sum := by decide
  have hdescent : baseEnd_3809058 < baseStart_3809058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809088 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2]
def baseStart_3809088 : Nat := 118140960795 + 3809088 * 2 ^ 59
def prefixEnd_3809088 : Nat := 4983230072969 + 3 ^ 40 * 3809088 * 2
def baseEnd_3809088 : Nat := 1955892999273298159382329

theorem tailTrace_3809088 : CollatzResearch.WordTrace tailWord_3809088 prefixEnd_3809088 1955892999273298159382329 := by
  unfold tailWord_3809088
  simp only [CollatzResearch.WordTrace]
  refine ⟨69464426412166095641669959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92619235216221460855559945 69464426412166095641669959)
  ·
    refine ⟨104196639618249143462504939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69464426412166095641669959 104196639618249143462504939)
    ·
      refine ⟨156294959427373715193757409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104196639618249143462504939 156294959427373715193757409)
      ·
        refine ⟨117221219570530286395318057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156294959427373715193757409 117221219570530286395318057)
        ·
          refine ⟨87915914677897714796488543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117221219570530286395318057 87915914677897714796488543)
          ·
            refine ⟨131873872016846572194732815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87915914677897714796488543 131873872016846572194732815)
            ·
              refine ⟨197810808025269858292099223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131873872016846572194732815 197810808025269858292099223)
              ·
                refine ⟨296716212037904787438148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197810808025269858292099223 296716212037904787438148835)
                ·
                  refine ⟨445074318056857181157223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296716212037904787438148835 445074318056857181157223253)
                  ·
                    refine ⟨2607857332364397545843105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 445074318056857181157223253 2607857332364397545843105)
                    ·
                      refine ⟨1955892999273298159382329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607857332364397545843105 1955892999273298159382329)
                      ·
                        rfl

theorem cell23_3809088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_3809088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809088 prefixEnd_3809088 := by exact prefixLift 3809088
  have htrace : WordTrace (prefixWord ++ tailWord_3809088) baseStart_3809088 baseEnd_3809088 := by
    simpa [prefixWord, tailWord_3809088, baseEnd_3809088] using wordTrace_append hprefix tailTrace_3809088
  have hstable : (prefixWord ++ tailWord_3809088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809088).length < 2 ^ (prefixWord ++ tailWord_3809088).sum := by decide
  have hdescent : baseEnd_3809088 < baseStart_3809088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809128 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3809128 : Nat := 118140960795 + 3809128 * 2 ^ 59
def prefixEnd_3809128 : Nat := 4983230072969 + 3 ^ 40 * 3809128 * 2
def baseEnd_3809128 : Nat := 651971179499826000960715

theorem tailTrace_3809128 : CollatzResearch.WordTrace tailWord_3809128 prefixEnd_3809128 651971179499826000960715 := by
  unfold tailWord_3809128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465155872093639057398019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92620207829458185409864025 69465155872093639057398019)
  ·
    refine ⟨104197733808140458586097029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69465155872093639057398019 104197733808140458586097029)
    ·
      refine ⟨19537075089026335984893193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104197733808140458586097029 19537075089026335984893193)
      ·
        refine ⟨14652806316769751988669895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19537075089026335984893193 14652806316769751988669895)
        ·
          refine ⟨21979209475154627983004843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652806316769751988669895 21979209475154627983004843)
          ·
            refine ⟨32968814212731941974507265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21979209475154627983004843 32968814212731941974507265)
            ·
              refine ⟨24726610659548956480880449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32968814212731941974507265 24726610659548956480880449)
              ·
                refine ⟨18544957994661717360660337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24726610659548956480880449 18544957994661717360660337)
                ·
                  refine ⟨13908718495996288020495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18544957994661717360660337 13908718495996288020495253)
                  ·
                    refine ⟨651971179499826000960715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13908718495996288020495253 651971179499826000960715)
                    ·
                      rfl

theorem cell23_3809128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3809128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809128 prefixEnd_3809128 := by exact prefixLift 3809128
  have htrace : WordTrace (prefixWord ++ tailWord_3809128) baseStart_3809128 baseEnd_3809128 := by
    simpa [prefixWord, tailWord_3809128, baseEnd_3809128] using wordTrace_append hprefix tailTrace_3809128
  have hstable : (prefixWord ++ tailWord_3809128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809128).length < 2 ^ (prefixWord ++ tailWord_3809128).sum := by decide
  have hdescent : baseEnd_3809128 < baseStart_3809128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809130 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3809130 : Nat := 118140960795 + 3809130 * 2 ^ 59
def prefixEnd_3809130 : Nat := 4983230072969 + 3 ^ 40 * 3809130 * 2
def baseEnd_3809130 : Nat := 1955914565460786995057137

theorem tailTrace_3809130 : CollatzResearch.WordTrace tailWord_3809130 prefixEnd_3809130 1955914565460786995057137 := by
  unfold tailWord_3809130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34732596172545008114092211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92620256460120021637579229 34732596172545008114092211)
  ·
    refine ⟨52098894258817512171138317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34732596172545008114092211 52098894258817512171138317)
    ·
      refine ⟨19537085347056567064176869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52098894258817512171138317 19537085347056567064176869)
      ·
        refine ⟨3663203502573106324533163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19537085347056567064176869 3663203502573106324533163)
        ·
          refine ⟨5494805253859659486799745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663203502573106324533163 5494805253859659486799745)
          ·
            refine ⟨4121103940394744615099809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494805253859659486799745 4121103940394744615099809)
            ·
              refine ⟨3090827955296058461324857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121103940394744615099809 3090827955296058461324857)
              ·
                refine ⟨2318120966472043845993643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090827955296058461324857 2318120966472043845993643)
                ·
                  refine ⟨3477181449708065768990465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318120966472043845993643 3477181449708065768990465)
                  ·
                    refine ⟨2607886087281049326742849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3477181449708065768990465 2607886087281049326742849)
                    ·
                      refine ⟨1955914565460786995057137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607886087281049326742849 1955914565460786995057137)
                      ·
                        rfl

theorem cell23_3809130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3809130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809130 prefixEnd_3809130 := by exact prefixLift 3809130
  have htrace : WordTrace (prefixWord ++ tailWord_3809130) baseStart_3809130 baseEnd_3809130 := by
    simpa [prefixWord, tailWord_3809130, baseEnd_3809130] using wordTrace_append hprefix tailTrace_3809130
  have hstable : (prefixWord ++ tailWord_3809130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809130).length < 2 ^ (prefixWord ++ tailWord_3809130).sum := by decide
  have hdescent : baseEnd_3809130 < baseStart_3809130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809131 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_3809131 : Nat := 118140960795 + 3809131 * 2 ^ 59
def prefixEnd_3809131 : Nat := 4983230072969 + 3 ^ 40 * 3809131 * 2
def baseEnd_3809131 : Nat := 1955915078941441491144631

theorem tailTrace_3809131 : CollatzResearch.WordTrace tailWord_3809131 prefixEnd_3809131 1955915078941441491144631 := by
  unfold tailWord_3809131
  simp only [CollatzResearch.WordTrace]
  refine ⟨138930421163176409627155247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92620280775450939751436831 138930421163176409627155247)
  ·
    refine ⟨208395631744764614440732871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138930421163176409627155247 208395631744764614440732871)
    ·
      refine ⟨312593447617146921661099307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208395631744764614440732871 312593447617146921661099307)
      ·
        refine ⟨468890171425720382491648961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312593447617146921661099307 468890171425720382491648961)
        ·
          refine ⟨351667628569290286868736721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468890171425720382491648961 351667628569290286868736721)
          ·
            refine ⟨263750721426967715151552541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351667628569290286868736721 263750721426967715151552541)
            ·
              refine ⟨98906520535112893181832203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263750721426967715151552541 98906520535112893181832203)
              ·
                refine ⟨148359780802669339772748305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98906520535112893181832203 148359780802669339772748305)
                ·
                  refine ⟨111269835602002004829561229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148359780802669339772748305 111269835602002004829561229)
                  ·
                    refine ⟨41726188350750751811085461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111269835602002004829561229 41726188350750751811085461)
                    ·
                      refine ⟨1955915078941441491144631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41726188350750751811085461 1955915078941441491144631)
                      ·
                        rfl

theorem cell23_3809131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_3809131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809131 prefixEnd_3809131 := by exact prefixLift 3809131
  have htrace : WordTrace (prefixWord ++ tailWord_3809131) baseStart_3809131 baseEnd_3809131 := by
    simpa [prefixWord, tailWord_3809131, baseEnd_3809131] using wordTrace_append hprefix tailTrace_3809131
  have hstable : (prefixWord ++ tailWord_3809131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809131).length < 2 ^ (prefixWord ++ tailWord_3809131).sum := by decide
  have hdescent : baseEnd_3809131 < baseStart_3809131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809152 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2]
def baseStart_3809152 : Nat := 118140960795 + 3809152 * 2 ^ 59
def prefixEnd_3809152 : Nat := 4983230072969 + 3 ^ 40 * 3809152 * 2
def baseEnd_3809152 : Nat := 1955925862035185908982035

theorem tailTrace_3809152 : CollatzResearch.WordTrace tailWord_3809152 prefixEnd_3809152 1955925862035185908982035 := by
  unfold tailWord_3809152
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465593548050165106834855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92620791397400220142446473 69465593548050165106834855)
  ·
    refine ⟨104198390322075247660252283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69465593548050165106834855 104198390322075247660252283)
    ·
      refine ⟨156297585483112871490378425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104198390322075247660252283 156297585483112871490378425)
      ·
        refine ⟨117223189112334653617783819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156297585483112871490378425 117223189112334653617783819)
        ·
          refine ⟨175834783668501980426675729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117223189112334653617783819 175834783668501980426675729)
          ·
            refine ⟨131876087751376485320006797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175834783668501980426675729 131876087751376485320006797)
            ·
              refine ⟨49453532906766181995002549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131876087751376485320006797 49453532906766181995002549)
              ·
                refine ⟨4636268710009329562031489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49453532906766181995002549 4636268710009329562031489)
                ·
                  refine ⟨3477201532506997171523617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636268710009329562031489 3477201532506997171523617)
                  ·
                    refine ⟨2607901149380247878642713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3477201532506997171523617 2607901149380247878642713)
                    ·
                      refine ⟨1955925862035185908982035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2607901149380247878642713 1955925862035185908982035)
                      ·
                        rfl

theorem cell23_3809152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_3809152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809152 prefixEnd_3809152 := by exact prefixLift 3809152
  have htrace : WordTrace (prefixWord ++ tailWord_3809152) baseStart_3809152 baseEnd_3809152 := by
    simpa [prefixWord, tailWord_3809152, baseEnd_3809152] using wordTrace_append hprefix tailTrace_3809152
  have hstable : (prefixWord ++ tailWord_3809152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809152).length < 2 ^ (prefixWord ++ tailWord_3809152).sum := by decide
  have hdescent : baseEnd_3809152 < baseStart_3809152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_3809168 : Nat := 118140960795 + 3809168 * 2 ^ 59
def prefixEnd_3809168 : Nat := 4983230072969 + 3 ^ 40 * 3809168 * 2
def baseEnd_3809168 : Nat := 1955934077725657846381961

theorem tailTrace_3809168 : CollatzResearch.WordTrace tailWord_3809168 prefixEnd_3809168 1955934077725657846381961 := by
  unfold tailWord_3809168
  simp only [CollatzResearch.WordTrace]
  refine ⟨69465885332021182473126079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92621180442694909964168105 69465885332021182473126079)
  ·
    refine ⟨104198827998031773709689119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69465885332021182473126079 104198827998031773709689119)
    ·
      refine ⟨156298241997047660564533679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104198827998031773709689119 156298241997047660564533679)
      ·
        refine ⟨234447362995571490846800519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156298241997047660564533679 234447362995571490846800519)
        ·
          refine ⟨351671044493357236270200779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234447362995571490846800519 351671044493357236270200779)
          ·
            refine ⟨527506566740035854405301169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351671044493357236270200779 527506566740035854405301169)
            ·
              refine ⟨395629925055026890803975877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527506566740035854405301169 395629925055026890803975877)
              ·
                refine ⟨74180610947817542025745477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395629925055026890803975877 74180610947817542025745477)
                ·
                  refine ⟨13908864552715789129827277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74180610947817542025745477 13908864552715789129827277)
                  ·
                    refine ⟨5215824207268420923685229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13908864552715789129827277 5215824207268420923685229)
                    ·
                      refine ⟨1955934077725657846381961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5215824207268420923685229 1955934077725657846381961)
                      ·
                        rfl

theorem cell23_3809168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_3809168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809168 prefixEnd_3809168 := by exact prefixLift 3809168
  have htrace : WordTrace (prefixWord ++ tailWord_3809168) baseStart_3809168 baseEnd_3809168 := by
    simpa [prefixWord, tailWord_3809168, baseEnd_3809168] using wordTrace_append hprefix tailTrace_3809168
  have hstable : (prefixWord ++ tailWord_3809168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809168).length < 2 ^ (prefixWord ++ tailWord_3809168).sum := by decide
  have hdescent : baseEnd_3809168 < baseStart_3809168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809175 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 5]
def baseStart_3809175 : Nat := 118140960795 + 3809175 * 2 ^ 59
def prefixEnd_3809175 : Nat := 4983230072969 + 3 ^ 40 * 3809175 * 2
def baseEnd_3809175 : Nat := 217326408010026590999381

theorem tailTrace_3809175 : CollatzResearch.WordTrace tailWord_3809175 prefixEnd_3809175 217326408010026590999381 := by
  unfold tailWord_3809175
  simp only [CollatzResearch.WordTrace]
  refine ⟨138932025975017005141756979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92621350650011336761171319 138932025975017005141756979)
  ·
    refine ⟨208398038962525507712635469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138932025975017005141756979 208398038962525507712635469)
    ·
      refine ⟨78149264610947065392238301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208398038962525507712635469 78149264610947065392238301)
      ·
        refine ⟨29305974229105149522089363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78149264610947065392238301 29305974229105149522089363)
        ·
          refine ⟨43958961343657724283134045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29305974229105149522089363 43958961343657724283134045)
          ·
            refine ⟨16484610503871646606175267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43958961343657724283134045 16484610503871646606175267)
            ·
              refine ⟨24726915755807469909262901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16484610503871646606175267 24726915755807469909262901)
              ·
                refine ⟨2318148352106950303993397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24726915755807469909262901 2318148352106950303993397)
                ·
                  refine ⟨217326408010026590999381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2318148352106950303993397 217326408010026590999381)
                  ·
                    rfl

theorem cell23_3809175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 5].length) (baseStart_3809175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809175 prefixEnd_3809175 := by exact prefixLift 3809175
  have htrace : WordTrace (prefixWord ++ tailWord_3809175) baseStart_3809175 baseEnd_3809175 := by
    simpa [prefixWord, tailWord_3809175, baseEnd_3809175] using wordTrace_append hprefix tailTrace_3809175
  have hstable : (prefixWord ++ tailWord_3809175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809175).length < 2 ^ (prefixWord ++ tailWord_3809175).sum := by decide
  have hdescent : baseEnd_3809175 < baseStart_3809175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809208 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_3809208 : Nat := 118140960795 + 3809208 * 2 ^ 59
def prefixEnd_3809208 : Nat := 4983230072969 + 3 ^ 40 * 3809208 * 2
def baseEnd_3809208 : Nat := 1955954616951837689881777

theorem tailTrace_3809208 : CollatzResearch.WordTrace tailWord_3809208 prefixEnd_3809208 1955954616951837689881777 := by
  unfold tailWord_3809208
  simp only [CollatzResearch.WordTrace]
  refine ⟨69466614791948725888854139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92622153055931634518472185 69466614791948725888854139)
  ·
    refine ⟨104199922187923088833281209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69466614791948725888854139 104199922187923088833281209)
    ·
      refine ⟨78149941640942316624960907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104199922187923088833281209 78149941640942316624960907)
      ·
        refine ⟨117224912461413474937441361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78149941640942316624960907 117224912461413474937441361)
        ·
          refine ⟨87918684346060106203081021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117224912461413474937441361 87918684346060106203081021)
          ·
            refine ⟨32969506629772539826155383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87918684346060106203081021 32969506629772539826155383)
            ·
              refine ⟨49454259944658809739233075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32969506629772539826155383 49454259944658809739233075)
              ·
                refine ⟨74181389916988214608849613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49454259944658809739233075 74181389916988214608849613)
                ·
                  refine ⟨27818021218870580478318605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74181389916988214608849613 27818021218870580478318605)
                  ·
                    refine ⟨10431757957076467679369477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27818021218870580478318605 10431757957076467679369477)
                    ·
                      refine ⟨1955954616951837689881777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10431757957076467679369477 1955954616951837689881777)
                      ·
                        rfl

theorem cell23_3809208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_3809208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809208 prefixEnd_3809208 := by exact prefixLift 3809208
  have htrace : WordTrace (prefixWord ++ tailWord_3809208) baseStart_3809208 baseEnd_3809208 := by
    simpa [prefixWord, tailWord_3809208, baseEnd_3809208] using wordTrace_append hprefix tailTrace_3809208
  have hstable : (prefixWord ++ tailWord_3809208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809208).length < 2 ^ (prefixWord ++ tailWord_3809208).sum := by decide
  have hdescent : baseEnd_3809208 < baseStart_3809208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809242 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_3809242 : Nat := 118140960795 + 3809242 * 2 ^ 59
def prefixEnd_3809242 : Nat := 4983230072969 + 3 ^ 40 * 3809242 * 2
def baseEnd_3809242 : Nat := 1955972075294090556856621

theorem tailTrace_3809242 : CollatzResearch.WordTrace tailWord_3809242 prefixEnd_3809242 1955972075294090556856621 := by
  unfold tailWord_3809242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733617416443568896111495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92622979777182850389630653 34733617416443568896111495)
  ·
    refine ⟨52100426124665353344167243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34733617416443568896111495 52100426124665353344167243)
    ·
      refine ⟨78150639186998030016250865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52100426124665353344167243 78150639186998030016250865)
      ·
        refine ⟨58612979390248522512188149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78150639186998030016250865 58612979390248522512188149)
        ·
          refine ⟨5494966817835798985517639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58612979390248522512188149 5494966817835798985517639)
          ·
            refine ⟨8242450226753698478276459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494966817835798985517639 8242450226753698478276459)
            ·
              refine ⟨12363675340130547717414689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242450226753698478276459 12363675340130547717414689)
              ·
                refine ⟨9272756505097910788061017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12363675340130547717414689 9272756505097910788061017)
                ·
                  refine ⟨6954567378823433091045763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272756505097910788061017 6954567378823433091045763)
                  ·
                    refine ⟨10431851068235149636568645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954567378823433091045763 10431851068235149636568645)
                    ·
                      refine ⟨1955972075294090556856621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10431851068235149636568645 1955972075294090556856621)
                      ·
                        rfl

theorem cell23_3809242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_3809242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809242 prefixEnd_3809242 := by exact prefixLift 3809242
  have htrace : WordTrace (prefixWord ++ tailWord_3809242) baseStart_3809242 baseEnd_3809242 := by
    simpa [prefixWord, tailWord_3809242, baseEnd_3809242] using wordTrace_append hprefix tailTrace_3809242
  have hstable : (prefixWord ++ tailWord_3809242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809242).length < 2 ^ (prefixWord ++ tailWord_3809242).sum := by decide
  have hdescent : baseEnd_3809242 < baseStart_3809242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809303 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 1, 4]
def baseStart_3809303 : Nat := 118140960795 + 3809303 * 2 ^ 59
def prefixEnd_3809303 : Nat := 4983230072969 + 3 ^ 40 * 3809303 * 2
def baseEnd_3809303 : Nat := 652001132538004939397947

theorem tailTrace_3809303 : CollatzResearch.WordTrace tailWord_3809303 prefixEnd_3809303 652001132538004939397947 := by
  unfold tailWord_3809303
  simp only [CollatzResearch.WordTrace]
  refine ⟨138936694518553283002416563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92624463012368855334944375 138936694518553283002416563)
  ·
    refine ⟨208405041777829924503624845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138936694518553283002416563 208405041777829924503624845)
    ·
      refine ⟨78151890666686221688859317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208405041777829924503624845 78151890666686221688859317)
      ·
        refine ⟨7326739750001833283330561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78151890666686221688859317 7326739750001833283330561)
        ·
          refine ⟨5495054812501374962497921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326739750001833283330561 5495054812501374962497921)
          ·
            refine ⟨4121291109376031221873441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495054812501374962497921 4121291109376031221873441)
            ·
              refine ⟨3090968332032023416405081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121291109376031221873441 3090968332032023416405081)
              ·
                refine ⟨2318226249024017562303811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090968332032023416405081 2318226249024017562303811)
                ·
                  refine ⟨3477339373536026343455717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318226249024017562303811 3477339373536026343455717)
                  ·
                    refine ⟨652001132538004939397947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477339373536026343455717 652001132538004939397947)
                    ·
                      rfl

theorem cell23_3809303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_3809303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809303 prefixEnd_3809303 := by exact prefixLift 3809303
  have htrace : WordTrace (prefixWord ++ tailWord_3809303) baseStart_3809303 baseEnd_3809303 := by
    simpa [prefixWord, tailWord_3809303, baseEnd_3809303] using wordTrace_append hprefix tailTrace_3809303
  have hstable : (prefixWord ++ tailWord_3809303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809303).length < 2 ^ (prefixWord ++ tailWord_3809303).sum := by decide
  have hdescent : baseEnd_3809303 < baseStart_3809303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809315 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3809315 : Nat := 118140960795 + 3809315 * 2 ^ 59
def prefixEnd_3809315 : Nat := 4983230072969 + 3 ^ 40 * 3809315 * 2
def baseEnd_3809315 : Nat := 1956009559381868771243785

theorem tailTrace_3809315 : CollatzResearch.WordTrace tailWord_3809315 prefixEnd_3809315 1956009559381868771243785 := by
  unfold tailWord_3809315
  simp only [CollatzResearch.WordTrace]
  refine ⟨138937132194509809051853399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92624754796339872701235599 138937132194509809051853399)
  ·
    refine ⟨208405698291764713577780099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138937132194509809051853399 208405698291764713577780099)
    ·
      refine ⟨312608547437647070366670149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208405698291764713577780099 312608547437647070366670149)
      ·
        refine ⟨58614102644558825693750653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312608547437647070366670149 58614102644558825693750653)
        ·
          refine ⟨21980288491709559635156495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58614102644558825693750653 21980288491709559635156495)
          ·
            refine ⟨32970432737564339452734743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980288491709559635156495 32970432737564339452734743)
            ·
              refine ⟨49455649106346509179102115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32970432737564339452734743 49455649106346509179102115)
              ·
                refine ⟨74183473659519763768653173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49455649106346509179102115 74183473659519763768653173)
                ·
                  refine ⟨6954700655579977853311235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74183473659519763768653173 6954700655579977853311235)
                  ·
                    refine ⟨10432050983369966779966853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6954700655579977853311235 10432050983369966779966853)
                    ·
                      refine ⟨1956009559381868771243785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10432050983369966779966853 1956009559381868771243785)
                      ·
                        rfl

theorem cell23_3809315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3809315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809315 prefixEnd_3809315 := by exact prefixLift 3809315
  have htrace : WordTrace (prefixWord ++ tailWord_3809315) baseStart_3809315 baseEnd_3809315 := by
    simpa [prefixWord, tailWord_3809315, baseEnd_3809315] using wordTrace_append hprefix tailTrace_3809315
  have hstable : (prefixWord ++ tailWord_3809315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809315).length < 2 ^ (prefixWord ++ tailWord_3809315).sum := by decide
  have hdescent : baseEnd_3809315 < baseStart_3809315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809336 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_3809336 : Nat := 118140960795 + 3809336 * 2 ^ 59
def prefixEnd_3809336 : Nat := 4983230072969 + 3 ^ 40 * 3809336 * 2
def baseEnd_3809336 : Nat := 1956020342475613189081189

theorem tailTrace_3809336 : CollatzResearch.WordTrace tailWord_3809336 prefixEnd_3809336 1956020342475613189081189 := by
  unfold tailWord_3809336
  simp only [CollatzResearch.WordTrace]
  refine ⟨69468949063716864819183931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92625265418289153092245241 69468949063716864819183931)
  ·
    refine ⟨104203423595575297228775897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69468949063716864819183931 104203423595575297228775897)
    ·
      refine ⟨78152567696681472921581923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104203423595575297228775897 78152567696681472921581923)
      ·
        refine ⟨117228851545022209382372885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78152567696681472921581923 117228851545022209382372885)
        ·
          refine ⟨5495102416172916064798729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117228851545022209382372885 5495102416172916064798729)
          ·
            refine ⟨4121326812129687048599047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495102416172916064798729 4121326812129687048599047)
            ·
              refine ⟨6181990218194530572898571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121326812129687048599047 6181990218194530572898571)
              ·
                refine ⟨9272985327291795859347857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181990218194530572898571 9272985327291795859347857)
                ·
                  refine ⟨6954738995468846894510893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272985327291795859347857 6954738995468846894510893)
                  ·
                    refine ⟨2608027123300817585441585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6954738995468846894510893 2608027123300817585441585)
                    ·
                      refine ⟨1956020342475613189081189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608027123300817585441585 1956020342475613189081189)
                      ·
                        rfl

theorem cell23_3809336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_3809336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809336 prefixEnd_3809336 := by exact prefixLift 3809336
  have htrace : WordTrace (prefixWord ++ tailWord_3809336) baseStart_3809336 baseEnd_3809336 := by
    simpa [prefixWord, tailWord_3809336, baseEnd_3809336] using wordTrace_append hprefix tailTrace_3809336
  have hstable : (prefixWord ++ tailWord_3809336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809336).length < 2 ^ (prefixWord ++ tailWord_3809336).sum := by decide
  have hdescent : baseEnd_3809336 < baseStart_3809336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809386 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3809386 : Nat := 118140960795 + 3809386 * 2 ^ 59
def prefixEnd_3809386 : Nat := 4983230072969 + 3 ^ 40 * 3809386 * 2
def baseEnd_3809386 : Nat := 1956046016508337993455959

theorem tailTrace_3809386 : CollatzResearch.WordTrace tailWord_3809386 prefixEnd_3809386 1956046016508337993455959 := by
  unfold tailWord_3809386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34734930444313147044422003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92626481184835058785125341 34734930444313147044422003)
  ·
    refine ⟨52102395666469720566633005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34734930444313147044422003 52102395666469720566633005)
    ·
      refine ⟨19538398374926145212487377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52102395666469720566633005 19538398374926145212487377)
      ·
        refine ⟨14653798781194608909365533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19538398374926145212487377 14653798781194608909365533)
        ·
          refine ⟨5495174542947978341012075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14653798781194608909365533 5495174542947978341012075)
          ·
            refine ⟨8242761814421967511518113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495174542947978341012075 8242761814421967511518113)
            ·
              refine ⟨6182071360816475633638585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242761814421967511518113 6182071360816475633638585)
              ·
                refine ⟨4636553520612356725228939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182071360816475633638585 4636553520612356725228939)
                ·
                  refine ⟨6954830280918535087843409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636553520612356725228939 6954830280918535087843409)
                  ·
                    refine ⟨5216122710688901315882557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954830280918535087843409 5216122710688901315882557)
                    ·
                      refine ⟨1956046016508337993455959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216122710688901315882557 1956046016508337993455959)
                      ·
                        rfl

theorem cell23_3809386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3809386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809386 prefixEnd_3809386 := by exact prefixLift 3809386
  have htrace : WordTrace (prefixWord ++ tailWord_3809386) baseStart_3809386 baseEnd_3809386 := by
    simpa [prefixWord, tailWord_3809386, baseEnd_3809386] using wordTrace_append hprefix tailTrace_3809386
  have hstable : (prefixWord ++ tailWord_3809386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809386).length < 2 ^ (prefixWord ++ tailWord_3809386).sum := by decide
  have hdescent : baseEnd_3809386 < baseStart_3809386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809415 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3809415 : Nat := 118140960795 + 3809415 * 2 ^ 59
def prefixEnd_3809415 : Nat := 4983230072969 + 3 ^ 40 * 3809415 * 2
def baseEnd_3809415 : Nat := 652020302482439459997775

theorem tailTrace_3809415 : CollatzResearch.WordTrace tailWord_3809415 prefixEnd_3809415 652020302482439459997775 := by
  unfold tailWord_3809415
  simp only [CollatzResearch.WordTrace]
  refine ⟨138940779494147526130493699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92627186329431684086995799 138940779494147526130493699)
  ·
    refine ⟨208411169241221289195740549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138940779494147526130493699 208411169241221289195740549)
    ·
      refine ⟨39077094232728991724201353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208411169241221289195740549 39077094232728991724201353)
      ·
        refine ⟨29307820674546743793151015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39077094232728991724201353 29307820674546743793151015)
        ·
          refine ⟨43961731011820115689726523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29307820674546743793151015 43961731011820115689726523)
          ·
            refine ⟨65942596517730173534589785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43961731011820115689726523 65942596517730173534589785)
            ·
              refine ⟨49456947388297630150942339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65942596517730173534589785 49456947388297630150942339)
              ·
                refine ⟨74185421082446445226413509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49456947388297630150942339 74185421082446445226413509)
                ·
                  refine ⟨13909766452958708479952533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74185421082446445226413509 13909766452958708479952533)
                  ·
                    refine ⟨652020302482439459997775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13909766452958708479952533 652020302482439459997775)
                    ·
                      rfl

theorem cell23_3809415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3809415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809415 prefixEnd_3809415 := by exact prefixLift 3809415
  have htrace : WordTrace (prefixWord ++ tailWord_3809415) baseStart_3809415 baseEnd_3809415 := by
    simpa [prefixWord, tailWord_3809415, baseEnd_3809415] using wordTrace_append hprefix tailTrace_3809415
  have hstable : (prefixWord ++ tailWord_3809415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809415).length < 2 ^ (prefixWord ++ tailWord_3809415).sum := by decide
  have hdescent : baseEnd_3809415 < baseStart_3809415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809445 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 9]
def baseStart_3809445 : Nat := 118140960795 + 3809445 * 2 ^ 59
def prefixEnd_3809445 : Nat := 4983230072969 + 3 ^ 40 * 3809445 * 2
def baseEnd_3809445 : Nat := 217341812429661473624243

theorem tailTrace_3809445 : CollatzResearch.WordTrace tailWord_3809445 prefixEnd_3809445 217341812429661473624243 := by
  unfold tailWord_3809445
  simp only [CollatzResearch.WordTrace]
  refine ⟨138941873684038841254085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92627915789359227502723859 138941873684038841254085789)
  ·
    refine ⟨52103202631514565470282171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138941873684038841254085789 52103202631514565470282171)
    ·
      refine ⟨78154803947271848205423257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52103202631514565470282171 78154803947271848205423257)
      ·
        refine ⟨58616102960453886154067443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78154803947271848205423257 58616102960453886154067443)
        ·
          refine ⟨87924154440680829231101165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58616102960453886154067443 87924154440680829231101165)
          ·
            refine ⟨32971557915255310961662937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87924154440680829231101165 32971557915255310961662937)
            ·
              refine ⟨24728668436441483221247203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32971557915255310961662937 24728668436441483221247203)
              ·
                refine ⟨37093002654662224831870805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24728668436441483221247203 37093002654662224831870805)
                ·
                  refine ⟨217341812429661473624243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37093002654662224831870805 217341812429661473624243)
                  ·
                    rfl

theorem cell23_3809445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_3809445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809445 prefixEnd_3809445 := by exact prefixLift 3809445
  have htrace : WordTrace (prefixWord ++ tailWord_3809445) baseStart_3809445 baseEnd_3809445 := by
    simpa [prefixWord, tailWord_3809445, baseEnd_3809445] using wordTrace_append hprefix tailTrace_3809445
  have hstable : (prefixWord ++ tailWord_3809445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809445).length < 2 ^ (prefixWord ++ tailWord_3809445).sum := by decide
  have hdescent : baseEnd_3809445 < baseStart_3809445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809509 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_3809509 : Nat := 118140960795 + 3809509 * 2 ^ 59
def prefixEnd_3809509 : Nat := 4983230072969 + 3 ^ 40 * 3809509 * 2
def baseEnd_3809509 : Nat := 652036391542947004072631

theorem tailTrace_3809509 : CollatzResearch.WordTrace tailWord_3809509 prefixEnd_3809509 652036391542947004072631 := by
  unfold tailWord_3809509
  simp only [CollatzResearch.WordTrace]
  refine ⟨138944207955806980184415581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92629471970537986789610387 138944207955806980184415581)
  ·
    refine ⟨52104077983427617569155843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138944207955806980184415581 52104077983427617569155843)
    ·
      refine ⟨78156116975141426353733765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52104077983427617569155843 78156116975141426353733765)
      ·
        refine ⟨14654271932839017441325081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78156116975141426353733765 14654271932839017441325081)
        ·
          refine ⟨10990703949629263080993811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14654271932839017441325081 10990703949629263080993811)
          ·
            refine ⟨16486055924443894621490717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990703949629263080993811 16486055924443894621490717)
            ·
              refine ⟨6182270971666460483059019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16486055924443894621490717 6182270971666460483059019)
              ·
                refine ⟨9273406457499690724588529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182270971666460483059019 9273406457499690724588529)
                ·
                  refine ⟨6955054843124768043441397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9273406457499690724588529 6955054843124768043441397)
                  ·
                    refine ⟨652036391542947004072631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6955054843124768043441397 652036391542947004072631)
                    ·
                      rfl

theorem cell23_3809509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_3809509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809509 prefixEnd_3809509 := by exact prefixLift 3809509
  have htrace : WordTrace (prefixWord ++ tailWord_3809509) baseStart_3809509 baseEnd_3809509 := by
    simpa [prefixWord, tailWord_3809509, baseEnd_3809509] using wordTrace_append hprefix tailTrace_3809509
  have hstable : (prefixWord ++ tailWord_3809509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809509).length < 2 ^ (prefixWord ++ tailWord_3809509).sum := by decide
  have hdescent : baseEnd_3809509 < baseStart_3809509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809539 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 3, 4]
def baseStart_3809539 : Nat := 118140960795 + 3809539 * 2 ^ 59
def prefixEnd_3809539 : Nat := 4983230072969 + 3 ^ 40 * 3809539 * 2
def baseEnd_3809539 : Nat := 652041526349491964947585

theorem tailTrace_3809539 : CollatzResearch.WordTrace tailWord_3809539 prefixEnd_3809539 652041526349491964947585 := by
  unfold tailWord_3809539
  simp only [CollatzResearch.WordTrace]
  refine ⟨138945302145698295308007671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92630201430465530205338447 138945302145698295308007671)
  ·
    refine ⟨208417953218547442962011507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138945302145698295308007671 208417953218547442962011507)
    ·
      refine ⟨312626929827821164443017261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208417953218547442962011507 312626929827821164443017261)
      ·
        refine ⟨117235098685432936666131473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312626929827821164443017261 117235098685432936666131473)
        ·
          refine ⟨87926324014074702499598605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117235098685432936666131473 87926324014074702499598605)
          ·
            refine ⟨32972371505278013437349477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87926324014074702499598605 32972371505278013437349477)
            ·
              refine ⟨6182319657239627519503027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32972371505278013437349477 6182319657239627519503027)
              ·
                refine ⟨9273479485859441279254541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182319657239627519503027 9273479485859441279254541)
                ·
                  refine ⟨3477554807197290479720453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9273479485859441279254541 3477554807197290479720453)
                  ·
                    refine ⟨652041526349491964947585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477554807197290479720453 652041526349491964947585)
                    ·
                      rfl

theorem cell23_3809539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 4].length) (baseStart_3809539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809539 prefixEnd_3809539 := by exact prefixLift 3809539
  have htrace : WordTrace (prefixWord ++ tailWord_3809539) baseStart_3809539 baseEnd_3809539 := by
    simpa [prefixWord, tailWord_3809539, baseEnd_3809539] using wordTrace_append hprefix tailTrace_3809539
  have hstable : (prefixWord ++ tailWord_3809539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809539).length < 2 ^ (prefixWord ++ tailWord_3809539).sum := by decide
  have hdescent : baseEnd_3809539 < baseStart_3809539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809616 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_3809616 : Nat := 118140960795 + 3809616 * 2 ^ 59
def prefixEnd_3809616 : Nat := 4983230072969 + 3 ^ 40 * 3809616 * 2
def baseEnd_3809616 : Nat := 652054705686290697859967

theorem tailTrace_3809616 : CollatzResearch.WordTrace tailWord_3809616 prefixEnd_3809616 652054705686290697859967 := by
  unfold tailWord_3809616
  simp only [CollatzResearch.WordTrace]
  refine ⟨69474055283209668729280351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92632073710946224972373801 69474055283209668729280351)
  ·
    refine ⟨104211082924814503093920527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69474055283209668729280351 104211082924814503093920527)
    ·
      refine ⟨156316624387221754640880791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104211082924814503093920527 156316624387221754640880791)
      ·
        refine ⟨234474936580832631961321187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156316624387221754640880791 234474936580832631961321187)
        ·
          refine ⟨351712404871248947941981781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234474936580832631961321187 351712404871248947941981781)
          ·
            refine ⟨4121629744584948608695099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 351712404871248947941981781 4121629744584948608695099)
            ·
              refine ⟨6182444616877422913042649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121629744584948608695099 6182444616877422913042649)
              ·
                refine ⟨4636833462658067184781987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182444616877422913042649 4636833462658067184781987)
                ·
                  refine ⟨6955250193987100777172981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636833462658067184781987 6955250193987100777172981)
                  ·
                    refine ⟨652054705686290697859967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6955250193987100777172981 652054705686290697859967)
                    ·
                      rfl

theorem cell23_3809616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_3809616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809616 prefixEnd_3809616 := by exact prefixLift 3809616
  have htrace : WordTrace (prefixWord ++ tailWord_3809616) baseStart_3809616 baseEnd_3809616 := by
    simpa [prefixWord, tailWord_3809616, baseEnd_3809616] using wordTrace_append hprefix tailTrace_3809616
  have hstable : (prefixWord ++ tailWord_3809616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809616).length < 2 ^ (prefixWord ++ tailWord_3809616).sum := by decide
  have hdescent : baseEnd_3809616 < baseStart_3809616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809619 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 4]
def baseStart_3809619 : Nat := 118140960795 + 3809619 * 2 ^ 59
def prefixEnd_3809619 : Nat := 4983230072969 + 3 ^ 40 * 3809619 * 2
def baseEnd_3809619 : Nat := 1956165657500835581842387

theorem tailTrace_3809619 : CollatzResearch.WordTrace tailWord_3809619 prefixEnd_3809619 1956165657500835581842387 := by
  unfold tailWord_3809619
  simp only [CollatzResearch.WordTrace]
  refine ⟨138948219985408468970919911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92632146656938979313946607 138948219985408468970919911)
  ·
    refine ⟨208422329978112703456379867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138948219985408468970919911 208422329978112703456379867)
    ·
      refine ⟨312633494967169055184569801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208422329978112703456379867 312633494967169055184569801)
      ·
        refine ⟨234475121225376791388427351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312633494967169055184569801 234475121225376791388427351)
        ·
          refine ⟨351712681838065187082641027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234475121225376791388427351 351712681838065187082641027)
          ·
            refine ⟨527569022757097780623961541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351712681838065187082641027 527569022757097780623961541)
            ·
              refine ⟨98919191766955833866992789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 527569022757097780623961541 98919191766955833866992789)
              ·
                refine ⟨4636837114076054712515287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98919191766955833866992789 4636837114076054712515287)
                ·
                  refine ⟨6955255671114082068772931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636837114076054712515287 6955255671114082068772931)
                  ·
                    refine ⟨10432883506671123103159397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955255671114082068772931 10432883506671123103159397)
                    ·
                      refine ⟨1956165657500835581842387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10432883506671123103159397 1956165657500835581842387)
                      ·
                        rfl

theorem cell23_3809619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_3809619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809619 prefixEnd_3809619 := by exact prefixLift 3809619
  have htrace : WordTrace (prefixWord ++ tailWord_3809619) baseStart_3809619 baseEnd_3809619 := by
    simpa [prefixWord, tailWord_3809619, baseEnd_3809619] using wordTrace_append hprefix tailTrace_3809619
  have hstable : (prefixWord ++ tailWord_3809619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809619).length < 2 ^ (prefixWord ++ tailWord_3809619).sum := by decide
  have hdescent : baseEnd_3809619 < baseStart_3809619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809659 : List Nat := [1, 1, 1, 1, 1, 9, 1, 8]
def baseStart_3809659 : Nat := 118140960795 + 3809659 * 2 ^ 59
def prefixEnd_3809659 : Nat := 4983230072969 + 3 ^ 40 * 3809659 * 2
def baseEnd_3809659 : Nat := 72451340619519089827489

theorem tailTrace_3809659 : CollatzResearch.WordTrace tailWord_3809659 prefixEnd_3809659 72451340619519089827489 := by
  unfold tailWord_3809659
  simp only [CollatzResearch.WordTrace]
  refine ⟨138949678905263555802376031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92633119270175703868250687 138949678905263555802376031)
  ·
    refine ⟨208424518357895333703564047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138949678905263555802376031 208424518357895333703564047)
    ·
      refine ⟨312636777536843000555346071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208424518357895333703564047 312636777536843000555346071)
      ·
        refine ⟨468955166305264500833019107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312636777536843000555346071 468955166305264500833019107)
        ·
          refine ⟨703432749457896751249528661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468955166305264500833019107 703432749457896751249528661)
          ·
            refine ⟨4121676266354863776852707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 703432749457896751249528661 4121676266354863776852707)
            ·
              refine ⟨6182514399532295665279061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121676266354863776852707 6182514399532295665279061)
              ·
                refine ⟨72451340619519089827489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6182514399532295665279061 72451340619519089827489)
                ·
                  rfl

theorem cell23_3809659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 8].length) (baseStart_3809659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809659 prefixEnd_3809659 := by exact prefixLift 3809659
  have htrace : WordTrace (prefixWord ++ tailWord_3809659) baseStart_3809659 baseEnd_3809659 := by
    simpa [prefixWord, tailWord_3809659, baseEnd_3809659] using wordTrace_append hprefix tailTrace_3809659
  have hstable : (prefixWord ++ tailWord_3809659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809659).length < 2 ^ (prefixWord ++ tailWord_3809659).sum := by decide
  have hdescent : baseEnd_3809659 < baseStart_3809659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809690 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3809690 : Nat := 118140960795 + 3809690 * 2 ^ 59
def prefixEnd_3809690 : Nat := 4983230072969 + 3 ^ 40 * 3809690 * 2
def baseEnd_3809690 : Nat := 1956202114627304804054561

theorem tailTrace_3809690 : CollatzResearch.WordTrace tailWord_3809690 prefixEnd_3809690 1956202114627304804054561 := by
  unfold tailWord_3809690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34737702392037812024188631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92633873045434165397836349 34737702392037812024188631)
  ·
    refine ⟨52106553588056718036282947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34737702392037812024188631 52106553588056718036282947)
    ·
      refine ⟨78159830382085077054424421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52106553588056718036282947 78159830382085077054424421)
      ·
        refine ⟨14654968196640951947704579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78159830382085077054424421 14654968196640951947704579)
        ·
          refine ⟨21982452294961427921556869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654968196640951947704579 21982452294961427921556869)
          ·
            refine ⟨4121709805305267735291913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21982452294961427921556869 4121709805305267735291913)
            ·
              refine ⟨3091282353978950801468935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121709805305267735291913 3091282353978950801468935)
              ·
                refine ⟨4636923530968426202203403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091282353978950801468935 4636923530968426202203403)
                ·
                  refine ⟨6955385296452639303305105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636923530968426202203403 6955385296452639303305105)
                  ·
                    refine ⟨5216538972339479477478829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955385296452639303305105 5216538972339479477478829)
                    ·
                      refine ⟨1956202114627304804054561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216538972339479477478829 1956202114627304804054561)
                      ·
                        rfl

theorem cell23_3809690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3809690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809690 prefixEnd_3809690 := by exact prefixLift 3809690
  have htrace : WordTrace (prefixWord ++ tailWord_3809690) baseStart_3809690 baseEnd_3809690 := by
    simpa [prefixWord, tailWord_3809690, baseEnd_3809690] using wordTrace_append hprefix tailTrace_3809690
  have hstable : (prefixWord ++ tailWord_3809690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809690).length < 2 ^ (prefixWord ++ tailWord_3809690).sum := by decide
  have hdescent : baseEnd_3809690 < baseStart_3809690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809697 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3809697 : Nat := 118140960795 + 3809697 * 2 ^ 59
def prefixEnd_3809697 : Nat := 4983230072969 + 3 ^ 40 * 3809697 * 2
def baseEnd_3809697 : Nat := 652068569663962092222343

theorem tailTrace_3809697 : CollatzResearch.WordTrace tailWord_3809697 prefixEnd_3809697 652068569663962092222343 := by
  unfold tailWord_3809697
  simp only [CollatzResearch.WordTrace]
  refine ⟨138951064879125888292259345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92634043252750592194839563 138951064879125888292259345)
  ·
    refine ⟨104213298659344416219194509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138951064879125888292259345 104213298659344416219194509)
    ·
      refine ⟨39079986997254156082197941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104213298659344416219194509 39079986997254156082197941)
      ·
        refine ⟨3663748780992577132706057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39079986997254156082197941 3663748780992577132706057)
        ·
          refine ⟨2747811585744432849529543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663748780992577132706057 2747811585744432849529543)
          ·
            refine ⟨4121717378616649274294315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747811585744432849529543 4121717378616649274294315)
            ·
              refine ⟨6182576067924973911441473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121717378616649274294315 6182576067924973911441473)
              ·
                refine ⟨4636932050943730433581105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182576067924973911441473 4636932050943730433581105)
                ·
                  refine ⟨3477699038207797825185829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636932050943730433581105 3477699038207797825185829)
                  ·
                    refine ⟨652068569663962092222343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477699038207797825185829 652068569663962092222343)
                    ·
                      rfl

theorem cell23_3809697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3809697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809697 prefixEnd_3809697 := by exact prefixLift 3809697
  have htrace : WordTrace (prefixWord ++ tailWord_3809697) baseStart_3809697 baseEnd_3809697 := by
    simpa [prefixWord, tailWord_3809697, baseEnd_3809697] using wordTrace_append hprefix tailTrace_3809697
  have hstable : (prefixWord ++ tailWord_3809697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809697).length < 2 ^ (prefixWord ++ tailWord_3809697).sum := by decide
  have hdescent : baseEnd_3809697 < baseStart_3809697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809703 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3809703 : Nat := 118140960795 + 3809703 * 2 ^ 59
def prefixEnd_3809703 : Nat := 4983230072969 + 3 ^ 40 * 3809703 * 2
def baseEnd_3809703 : Nat := 1956208789875813253192001

theorem tailTrace_3809703 : CollatzResearch.WordTrace tailWord_3809703 prefixEnd_3809703 1956208789875813253192001 := by
  unfold tailWord_3809703
  simp only [CollatzResearch.WordTrace]
  refine ⟨138951283717104151316977763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92634189144736100877985175 138951283717104151316977763)
  ·
    refine ⟨208426925575656226975466645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138951283717104151316977763 208426925575656226975466645)
    ·
      refine ⟨9770012136358885639474999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208426925575656226975466645 9770012136358885639474999)
      ·
        refine ⟨14655018204538328459212499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770012136358885639474999 14655018204538328459212499)
        ·
          refine ⟨21982527306807492688818749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655018204538328459212499 21982527306807492688818749)
          ·
            refine ⟨8243447740052809758307031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21982527306807492688818749 8243447740052809758307031)
            ·
              refine ⟨12365171610079214637460547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243447740052809758307031 12365171610079214637460547)
              ·
                refine ⟨18547757415118821956190821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365171610079214637460547 18547757415118821956190821)
                ·
                  refine ⟨3477704515334779116785779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18547757415118821956190821 3477704515334779116785779)
                  ·
                    refine ⟨5216556773002168675178669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3477704515334779116785779 5216556773002168675178669)
                    ·
                      refine ⟨1956208789875813253192001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216556773002168675178669 1956208789875813253192001)
                      ·
                        rfl

theorem cell23_3809703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3809703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809703 prefixEnd_3809703 := by exact prefixLift 3809703
  have htrace : WordTrace (prefixWord ++ tailWord_3809703) baseStart_3809703 baseEnd_3809703 := by
    simpa [prefixWord, tailWord_3809703, baseEnd_3809703] using wordTrace_append hprefix tailTrace_3809703
  have hstable : (prefixWord ++ tailWord_3809703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809703).length < 2 ^ (prefixWord ++ tailWord_3809703).sum := by decide
  have hdescent : baseEnd_3809703 < baseStart_3809703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809719 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 6]
def baseStart_3809719 : Nat := 118140960795 + 3809719 * 2 ^ 59
def prefixEnd_3809719 : Nat := 4983230072969 + 3 ^ 40 * 3809719 * 2
def baseEnd_3809719 : Nat := 652072335188761730197309

theorem tailTrace_3809719 : CollatzResearch.WordTrace tailWord_3809719 prefixEnd_3809719 652072335188761730197309 := by
  unfold tailWord_3809719
  simp only [CollatzResearch.WordTrace]
  refine ⟨138951867285046186049560211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92634578190030790699706807 138951867285046186049560211)
  ·
    refine ⟨208427800927569279074340317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138951867285046186049560211 208427800927569279074340317)
    ·
      refine ⟨78160425347838479652877619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208427800927569279074340317 78160425347838479652877619)
      ·
        refine ⟨117240638021757719479316429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78160425347838479652877619 117240638021757719479316429)
        ·
          refine ⟨43965239258159144804743661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117240638021757719479316429 43965239258159144804743661)
          ·
            refine ⟨16486964721809679301778873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43965239258159144804743661 16486964721809679301778873)
            ·
              refine ⟨12365223541357259476334155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16486964721809679301778873 12365223541357259476334155)
              ·
                refine ⟨18547835312035889214501233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365223541357259476334155 18547835312035889214501233)
                ·
                  refine ⟨13910876484026916910875925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18547835312035889214501233 13910876484026916910875925)
                  ·
                    refine ⟨652072335188761730197309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13910876484026916910875925 652072335188761730197309)
                    ·
                      rfl

theorem cell23_3809719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_3809719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809719 prefixEnd_3809719 := by exact prefixLift 3809719
  have htrace : WordTrace (prefixWord ++ tailWord_3809719) baseStart_3809719 baseEnd_3809719 := by
    simpa [prefixWord, tailWord_3809719, baseEnd_3809719] using wordTrace_append hprefix tailTrace_3809719
  have hstable : (prefixWord ++ tailWord_3809719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809719).length < 2 ^ (prefixWord ++ tailWord_3809719).sum := by decide
  have hdescent : baseEnd_3809719 < baseStart_3809719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809779 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 4, 5]
def baseStart_3809779 : Nat := 118140960795 + 3809779 * 2 ^ 59
def prefixEnd_3809779 : Nat := 4983230072969 + 3 ^ 40 * 3809779 * 2
def baseEnd_3809779 : Nat := 652082604801851651947217

theorem tailTrace_3809779 : CollatzResearch.WordTrace tailWord_3809779 prefixEnd_3809779 652082604801851651947217 := by
  unfold tailWord_3809779
  simp only [CollatzResearch.WordTrace]
  refine ⟨138954055664828816296744391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92636037109885877531162927 138954055664828816296744391)
  ·
    refine ⟨208431083497243224445116587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138954055664828816296744391 208431083497243224445116587)
    ·
      refine ⟨312646625245864836667674881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208431083497243224445116587 312646625245864836667674881)
      ·
        refine ⟨234484968934398627500756161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312646625245864836667674881 234484968934398627500756161)
        ·
          refine ⟨175863726700798970625567121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234484968934398627500756161 175863726700798970625567121)
          ·
            refine ⟨131897795025599227969175341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175863726700798970625567121 131897795025599227969175341)
            ·
              refine ⟨49461673134599710488440753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131897795025599227969175341 49461673134599710488440753)
              ·
                refine ⟨37096254850949782866330565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49461673134599710488440753 37096254850949782866330565)
                ·
                  refine ⟨6955547784553084287436981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37096254850949782866330565 6955547784553084287436981)
                  ·
                    refine ⟨652082604801851651947217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6955547784553084287436981 652082604801851651947217)
                    ·
                      rfl

theorem cell23_3809779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 5].length) (baseStart_3809779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809779 prefixEnd_3809779 := by exact prefixLift 3809779
  have htrace : WordTrace (prefixWord ++ tailWord_3809779) baseStart_3809779 baseEnd_3809779 := by
    simpa [prefixWord, tailWord_3809779, baseEnd_3809779] using wordTrace_append hprefix tailTrace_3809779
  have hstable : (prefixWord ++ tailWord_3809779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809779).length < 2 ^ (prefixWord ++ tailWord_3809779).sum := by decide
  have hdescent : baseEnd_3809779 < baseStart_3809779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809786 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_3809786 : Nat := 118140960795 + 3809786 * 2 ^ 59
def prefixEnd_3809786 : Nat := 4983230072969 + 3 ^ 40 * 3809786 * 2
def baseEnd_3809786 : Nat := 1956251408770136428454119

theorem tailTrace_3809786 : CollatzResearch.WordTrace tailWord_3809786 prefixEnd_3809786 1956251408770136428454119 := by
  unfold tailWord_3809786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34738577743950864123062303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92636207317202304328166141 34738577743950864123062303)
  ·
    refine ⟨52107866615926296184593455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34738577743950864123062303 52107866615926296184593455)
    ·
      refine ⟨78161799923889444276890183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52107866615926296184593455 78161799923889444276890183)
      ·
        refine ⟨117242699885834166415335275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78161799923889444276890183 117242699885834166415335275)
        ·
          refine ⟨175864049828751249623002913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117242699885834166415335275 175864049828751249623002913)
          ·
            refine ⟨131898037371563437217252185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175864049828751249623002913 131898037371563437217252185)
            ·
              refine ⟨98923528028672577912939139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131898037371563437217252185 98923528028672577912939139)
              ·
                refine ⟨148385292043008866869408709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98923528028672577912939139 148385292043008866869408709)
                ·
                  refine ⟨27822242258064162538014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148385292043008866869408709 27822242258064162538014133)
                  ·
                    refine ⟨2608335211693515237938825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27822242258064162538014133 2608335211693515237938825)
                    ·
                      refine ⟨1956251408770136428454119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608335211693515237938825 1956251408770136428454119)
                      ·
                        rfl

theorem cell23_3809786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_3809786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809786 prefixEnd_3809786 := by exact prefixLift 3809786
  have htrace : WordTrace (prefixWord ++ tailWord_3809786) baseStart_3809786 baseEnd_3809786 := by
    simpa [prefixWord, tailWord_3809786, baseEnd_3809786] using wordTrace_append hprefix tailTrace_3809786
  have hstable : (prefixWord ++ tailWord_3809786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809786).length < 2 ^ (prefixWord ++ tailWord_3809786).sum := by decide
  have hdescent : baseEnd_3809786 < baseStart_3809786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809789 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3809789 : Nat := 118140960795 + 3809789 * 2 ^ 59
def prefixEnd_3809789 : Nat := 4983230072969 + 3 ^ 40 * 3809789 * 2
def baseEnd_3809789 : Nat := 1956252949212099916716605

theorem tailTrace_3809789 : CollatzResearch.WordTrace tailWord_3809789 prefixEnd_3809789 1956252949212099916716605 := by
  unfold tailWord_3809789
  simp only [CollatzResearch.WordTrace]
  refine ⟨138954420394792588004608421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92636280263195058669738947 138954420394792588004608421)
  ·
    refine ⟨26053953824023610250864079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138954420394792588004608421 26053953824023610250864079)
    ·
      refine ⟨39080930736035415376296119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26053953824023610250864079 39080930736035415376296119)
      ·
        refine ⟨58621396104053123064444179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39080930736035415376296119 58621396104053123064444179)
        ·
          refine ⟨87932094156079684596666269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58621396104053123064444179 87932094156079684596666269)
          ·
            refine ⟨32974535308529881723749851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87932094156079684596666269 32974535308529881723749851)
            ·
              refine ⟨49461802962794822585624777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32974535308529881723749851 49461802962794822585624777)
              ·
                refine ⟨37096352222096116939218583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49461802962794822585624777 37096352222096116939218583)
                ·
                  refine ⟨55644528333144175408827875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37096352222096116939218583 55644528333144175408827875)
                  ·
                    refine ⟨83466792499716263113241813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55644528333144175408827875 83466792499716263113241813)
                    ·
                      refine ⟨1956252949212099916716605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83466792499716263113241813 1956252949212099916716605)
                      ·
                        rfl

theorem cell23_3809789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3809789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809789 prefixEnd_3809789 := by exact prefixLift 3809789
  have htrace : WordTrace (prefixWord ++ tailWord_3809789) baseStart_3809789 baseEnd_3809789 := by
    simpa [prefixWord, tailWord_3809789, baseEnd_3809789] using wordTrace_append hprefix tailTrace_3809789
  have hstable : (prefixWord ++ tailWord_3809789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809789).length < 2 ^ (prefixWord ++ tailWord_3809789).sum := by decide
  have hdescent : baseEnd_3809789 < baseStart_3809789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809806 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3809806 : Nat := 118140960795 + 3809806 * 2 ^ 59
def prefixEnd_3809806 : Nat := 4983230072969 + 3 ^ 40 * 3809806 * 2
def baseEnd_3809806 : Nat := 1956261678383226350204027

theorem tailTrace_3809806 : CollatzResearch.WordTrace tailWord_3809806 prefixEnd_3809806 1956261678383226350204027 := by
  unfold tailWord_3809806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369380054466374988497159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92636693623820666605318181 17369380054466374988497159)
  ·
    refine ⟨26054070081699562482745739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17369380054466374988497159 26054070081699562482745739)
    ·
      refine ⟨39081105122549343724118609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26054070081699562482745739 39081105122549343724118609)
      ·
        refine ⟨29310828841912007793088957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39081105122549343724118609 29310828841912007793088957)
        ·
          refine ⟨10991560815717002922408359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29310828841912007793088957 10991560815717002922408359)
          ·
            refine ⟨16487341223575504383612539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991560815717002922408359 16487341223575504383612539)
            ·
              refine ⟨24731011835363256575418809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16487341223575504383612539 24731011835363256575418809)
              ·
                refine ⟨18548258876522442431564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24731011835363256575418809 18548258876522442431564107)
                ·
                  refine ⟨27822388314783663647346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548258876522442431564107 27822388314783663647346161)
                  ·
                    refine ⟨20866791236087747735509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27822388314783663647346161 20866791236087747735509621)
                    ·
                      refine ⟨1956261678383226350204027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20866791236087747735509621 1956261678383226350204027)
                      ·
                        rfl

theorem cell23_3809806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3809806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809806 prefixEnd_3809806 := by exact prefixLift 3809806
  have htrace : WordTrace (prefixWord ++ tailWord_3809806) baseStart_3809806 baseEnd_3809806 := by
    simpa [prefixWord, tailWord_3809806, baseEnd_3809806] using wordTrace_append hprefix tailTrace_3809806
  have hstable : (prefixWord ++ tailWord_3809806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809806).length < 2 ^ (prefixWord ++ tailWord_3809806).sum := by decide
  have hdescent : baseEnd_3809806 < baseStart_3809806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809836 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_3809836 : Nat := 118140960795 + 3809836 * 2 ^ 59
def prefixEnd_3809836 : Nat := 4983230072969 + 3 ^ 40 * 3809836 * 2
def baseEnd_3809836 : Nat := 1956277082802861232828889

theorem tailTrace_3809836 : CollatzResearch.WordTrace tailWord_3809836 prefixEnd_3809836 1956277082802861232828889 := by
  unfold tailWord_3809836
  simp only [CollatzResearch.WordTrace]
  refine ⟨69478067312811157515784681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92637423083748210021046241 69478067312811157515784681)
  ·
    refine ⟨52108550484608368136838511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69478067312811157515784681 52108550484608368136838511)
    ·
      refine ⟨78162825726912552205257767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52108550484608368136838511 78162825726912552205257767)
      ·
        refine ⟨117244238590368828307886651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78162825726912552205257767 117244238590368828307886651)
        ·
          refine ⟨175866357885553242461829977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117244238590368828307886651 175866357885553242461829977)
          ·
            refine ⟨131899768414164931846372483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175866357885553242461829977 131899768414164931846372483)
            ·
              refine ⟨197849652621247397769558725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131899768414164931846372483 197849652621247397769558725)
              ·
                refine ⟨37096809866483887081792261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197849652621247397769558725 37096809866483887081792261)
                ·
                  refine ⟨6955651849965728827836049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37096809866483887081792261 6955651849965728827836049)
                  ·
                    refine ⟨5216738887474296620877037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955651849965728827836049 5216738887474296620877037)
                    ·
                      refine ⟨1956277082802861232828889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216738887474296620877037 1956277082802861232828889)
                      ·
                        rfl

theorem cell23_3809836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_3809836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809836 prefixEnd_3809836 := by exact prefixLift 3809836
  have htrace : WordTrace (prefixWord ++ tailWord_3809836) baseStart_3809836 baseEnd_3809836 := by
    simpa [prefixWord, tailWord_3809836, baseEnd_3809836] using wordTrace_append hprefix tailTrace_3809836
  have hstable : (prefixWord ++ tailWord_3809836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809836).length < 2 ^ (prefixWord ++ tailWord_3809836).sum := by decide
  have hdescent : baseEnd_3809836 < baseStart_3809836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809853 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3809853 : Nat := 118140960795 + 3809853 * 2 ^ 59
def prefixEnd_3809853 : Nat := 4983230072969 + 3 ^ 40 * 3809853 * 2
def baseEnd_3809853 : Nat := 1956285811973987666316311

theorem tailTrace_3809853 : CollatzResearch.WordTrace tailWord_3809853 prefixEnd_3809853 1956285811973987666316311 := by
  unfold tailWord_3809853
  simp only [CollatzResearch.WordTrace]
  refine ⟨138956754666560726934938213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92637836444373817956625475 138956754666560726934938213)
  ·
    refine ⟨26054391499980136300300915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138956754666560726934938213 26054391499980136300300915)
    ·
      refine ⟨39081587249970204450451373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26054391499980136300300915 39081587249970204450451373)
      ·
        refine ⟨14655595218738826668919265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39081587249970204450451373 14655595218738826668919265)
        ·
          refine ⟨10991696414054120001689449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14655595218738826668919265 10991696414054120001689449)
          ·
            refine ⟨8243772310540590001267087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10991696414054120001689449 8243772310540590001267087)
            ·
              refine ⟨12365658465810885001900631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243772310540590001267087 12365658465810885001900631)
              ·
                refine ⟨18548487698716327502850947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365658465810885001900631 18548487698716327502850947)
                ·
                  refine ⟨27822731548074491254276421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548487698716327502850947 27822731548074491254276421)
                  ·
                    refine ⟨5216762165263967110176829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27822731548074491254276421 5216762165263967110176829)
                    ·
                      refine ⟨1956285811973987666316311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216762165263967110176829 1956285811973987666316311)
                      ·
                        rfl

theorem cell23_3809853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3809853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809853 prefixEnd_3809853 := by exact prefixLift 3809853
  have htrace : WordTrace (prefixWord ++ tailWord_3809853) baseStart_3809853 baseEnd_3809853 := by
    simpa [prefixWord, tailWord_3809853, baseEnd_3809853] using wordTrace_append hprefix tailTrace_3809853
  have hstable : (prefixWord ++ tailWord_3809853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809853).length < 2 ^ (prefixWord ++ tailWord_3809853).sum := by decide
  have hdescent : baseEnd_3809853 < baseStart_3809853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809859 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_3809859 : Nat := 118140960795 + 3809859 * 2 ^ 59
def prefixEnd_3809859 : Nat := 4983230072969 + 3 ^ 40 * 3809859 * 2
def baseEnd_3809859 : Nat := 1956288892857914642841283

theorem tailTrace_3809859 : CollatzResearch.WordTrace tailWord_3809859 prefixEnd_3809859 1956288892857914642841283 := by
  unfold tailWord_3809859
  simp only [CollatzResearch.WordTrace]
  refine ⟨138956973504538989959656631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92637982336359326639771087 138956973504538989959656631)
  ·
    refine ⟨208435460256808484939484947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138956973504538989959656631 208435460256808484939484947)
    ·
      refine ⟨312653190385212727409227421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208435460256808484939484947 312653190385212727409227421)
      ·
        refine ⟨117244946394454772778460283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312653190385212727409227421 117244946394454772778460283)
        ·
          refine ⟨175867419591682159167690425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117244946394454772778460283 175867419591682159167690425)
          ·
            refine ⟨131900564693761619375767819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175867419591682159167690425 131900564693761619375767819)
            ·
              refine ⟨197850847040642429063651729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131900564693761619375767819 197850847040642429063651729)
              ·
                refine ⟨148388135280481821797738797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197850847040642429063651729 148388135280481821797738797)
                ·
                  refine ⟨55645550730180683174152049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148388135280481821797738797 55645550730180683174152049)
                  ·
                    refine ⟨41734163047635512380614037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55645550730180683174152049 41734163047635512380614037)
                    ·
                      refine ⟨1956288892857914642841283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41734163047635512380614037 1956288892857914642841283)
                      ·
                        rfl

theorem cell23_3809859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_3809859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809859 prefixEnd_3809859 := by exact prefixLift 3809859
  have htrace : WordTrace (prefixWord ++ tailWord_3809859) baseStart_3809859 baseEnd_3809859 := by
    simpa [prefixWord, tailWord_3809859, baseEnd_3809859] using wordTrace_append hprefix tailTrace_3809859
  have hstable : (prefixWord ++ tailWord_3809859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809859).length < 2 ^ (prefixWord ++ tailWord_3809859).sum := by decide
  have hdescent : baseEnd_3809859 < baseStart_3809859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809873 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 6]
def baseStart_3809873 : Nat := 118140960795 + 3809873 * 2 ^ 59
def prefixEnd_3809873 : Nat := 4983230072969 + 3 ^ 40 * 3809873 * 2
def baseEnd_3809873 : Nat := 217366231287453065340691

theorem tailTrace_3809873 : CollatzResearch.WordTrace tailWord_3809873 prefixEnd_3809873 217366231287453065340691 := by
  unfold tailWord_3809873
  simp only [CollatzResearch.WordTrace]
  refine ⟨138957484126488270350666273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92638322750992180233777515 138957484126488270350666273)
  ·
    refine ⟨104218113094866202762999705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138957484126488270350666273 104218113094866202762999705)
    ·
      refine ⟨78163584821149652072249779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104218113094866202762999705 78163584821149652072249779)
      ·
        refine ⟨117245377231724478108374669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78163584821149652072249779 117245377231724478108374669)
        ·
          refine ⟨43967016461896679290640501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117245377231724478108374669 43967016461896679290640501)
          ·
            refine ⟨4121907793302813683497547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43967016461896679290640501 4121907793302813683497547)
            ·
              refine ⟨6182861689954220525246321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121907793302813683497547 6182861689954220525246321)
              ·
                refine ⟨4637146267465665393934741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182861689954220525246321 4637146267465665393934741)
                ·
                  refine ⟨217366231287453065340691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4637146267465665393934741 217366231287453065340691)
                  ·
                    rfl

theorem cell23_3809873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_3809873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809873 prefixEnd_3809873 := by exact prefixLift 3809873
  have htrace : WordTrace (prefixWord ++ tailWord_3809873) baseStart_3809873 baseEnd_3809873 := by
    simpa [prefixWord, tailWord_3809873, baseEnd_3809873] using wordTrace_append hprefix tailTrace_3809873
  have hstable : (prefixWord ++ tailWord_3809873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809873).length < 2 ^ (prefixWord ++ tailWord_3809873).sum := by decide
  have hdescent : baseEnd_3809873 < baseStart_3809873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809876 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3809876 : Nat := 118140960795 + 3809876 * 2 ^ 59
def prefixEnd_3809876 : Nat := 4983230072969 + 3 ^ 40 * 3809876 * 2
def baseEnd_3809876 : Nat := 1956297622029041076328705

theorem tailTrace_3809876 : CollatzResearch.WordTrace tailWord_3809876 prefixEnd_3809876 1956297622029041076328705 := by
  unfold tailWord_3809876
  simp only [CollatzResearch.WordTrace]
  refine ⟨69478796772738700931512741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92638395696984934575350321 69478796772738700931512741)
  ·
    refine ⟨13027274394888506424658639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69478796772738700931512741 13027274394888506424658639)
    ·
      refine ⟨19540911592332759636987959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13027274394888506424658639 19540911592332759636987959)
      ·
        refine ⟨29311367388499139455481939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19540911592332759636987959 29311367388499139455481939)
        ·
          refine ⟨43967051082748709183222909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29311367388499139455481939 43967051082748709183222909)
          ·
            refine ⟨16487644156030765943708591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43967051082748709183222909 16487644156030765943708591)
            ·
              refine ⟨24731466234046148915562887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16487644156030765943708591 24731466234046148915562887)
              ·
                refine ⟨37097199351069223373344331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24731466234046148915562887 37097199351069223373344331)
                ·
                  refine ⟨55645799026603835060016497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37097199351069223373344331 55645799026603835060016497)
                  ·
                    refine ⟨41734349269952876295012373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55645799026603835060016497 41734349269952876295012373)
                    ·
                      refine ⟨1956297622029041076328705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41734349269952876295012373 1956297622029041076328705)
                      ·
                        rfl

theorem cell23_3809876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3809876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809876 prefixEnd_3809876 := by exact prefixLift 3809876
  have htrace : WordTrace (prefixWord ++ tailWord_3809876) baseStart_3809876 baseEnd_3809876 := by
    simpa [prefixWord, tailWord_3809876, baseEnd_3809876] using wordTrace_append hprefix tailTrace_3809876
  have hstable : (prefixWord ++ tailWord_3809876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809876).length < 2 ^ (prefixWord ++ tailWord_3809876).sum := by decide
  have hdescent : baseEnd_3809876 < baseStart_3809876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809916 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_3809916 : Nat := 118140960795 + 3809916 * 2 ^ 59
def prefixEnd_3809916 : Nat := 4983230072969 + 3 ^ 40 * 3809916 * 2
def baseEnd_3809916 : Nat := 652106053751740306609507

theorem tailTrace_3809916 : CollatzResearch.WordTrace tailWord_3809916 prefixEnd_3809916 652106053751740306609507 := by
  unfold tailWord_3809916
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479526232666244347240801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92639368310221659129654401 69479526232666244347240801)
  ·
    refine ⟨52109644674499683260430601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69479526232666244347240801 52109644674499683260430601)
    ·
      refine ⟨39082233505874762445322951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52109644674499683260430601 39082233505874762445322951)
      ·
        refine ⟨58623350258812143667984427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39082233505874762445322951 58623350258812143667984427)
        ·
          refine ⟨87935025388218215501976641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58623350258812143667984427 87935025388218215501976641)
          ·
            refine ⟨65951269041163661626482481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87935025388218215501976641 65951269041163661626482481)
            ·
              refine ⟨49463451780872746219861861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65951269041163661626482481 49463451780872746219861861)
              ·
                refine ⟨9274397208913639916224099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49463451780872746219861861 9274397208913639916224099)
                ·
                  refine ⟨13911595813370459874336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274397208913639916224099 13911595813370459874336149)
                  ·
                    refine ⟨652106053751740306609507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13911595813370459874336149 652106053751740306609507)
                    ·
                      rfl

theorem cell23_3809916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_3809916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809916 prefixEnd_3809916 := by exact prefixLift 3809916
  have htrace : WordTrace (prefixWord ++ tailWord_3809916) baseStart_3809916 baseEnd_3809916 := by
    simpa [prefixWord, tailWord_3809916, baseEnd_3809916] using wordTrace_append hprefix tailTrace_3809916
  have hstable : (prefixWord ++ tailWord_3809916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809916).length < 2 ^ (prefixWord ++ tailWord_3809916).sum := by decide
  have hdescent : baseEnd_3809916 < baseStart_3809916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809923 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 4]
def baseStart_3809923 : Nat := 118140960795 + 3809923 * 2 ^ 59
def prefixEnd_3809923 : Nat := 4983230072969 + 3 ^ 40 * 3809923 * 2
def baseEnd_3809923 : Nat := 1956321755619802392440989

theorem tailTrace_3809923 : CollatzResearch.WordTrace tailWord_3809923 prefixEnd_3809923 1956321755619802392440989 := by
  unfold tailWord_3809923
  simp only [CollatzResearch.WordTrace]
  refine ⟨138959307776307128889986423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92639538517538085926657615 138959307776307128889986423)
  ·
    refine ⟨208438961664460693334979635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138959307776307128889986423 208438961664460693334979635)
    ·
      refine ⟨312658442496691040002469453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208438961664460693334979635 312658442496691040002469453)
      ·
        refine ⟨117246915936259140000926045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312658442496691040002469453 117246915936259140000926045)
        ·
          refine ⟨43967593476097177500347267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117246915936259140000926045 43967593476097177500347267)
          ·
            refine ⟨65951390214145766250520901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43967593476097177500347267 65951390214145766250520901)
            ·
              refine ⟨12365885665152331171972669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65951390214145766250520901 12365885665152331171972669)
              ·
                refine ⟨4637207124432124189489751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12365885665152331171972669 4637207124432124189489751)
                ·
                  refine ⟨6955810686648186284234627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637207124432124189489751 6955810686648186284234627)
                  ·
                    refine ⟨10433716029972279426351941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6955810686648186284234627 10433716029972279426351941)
                    ·
                      refine ⟨1956321755619802392440989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10433716029972279426351941 1956321755619802392440989)
                      ·
                        rfl

theorem cell23_3809923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_3809923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809923 prefixEnd_3809923 := by exact prefixLift 3809923
  have htrace : WordTrace (prefixWord ++ tailWord_3809923) baseStart_3809923 baseEnd_3809923 := by
    simpa [prefixWord, tailWord_3809923, baseEnd_3809923] using wordTrace_append hprefix tailTrace_3809923
  have hstable : (prefixWord ++ tailWord_3809923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809923).length < 2 ^ (prefixWord ++ tailWord_3809923).sum := by decide
  have hdescent : baseEnd_3809923 < baseStart_3809923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809934 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3809934 : Nat := 118140960795 + 3809934 * 2 ^ 59
def prefixEnd_3809934 : Nat := 4983230072969 + 3 ^ 40 * 3809934 * 2
def baseEnd_3809934 : Nat := 1956327403907001849403439

theorem tailTrace_3809934 : CollatzResearch.WordTrace tailWord_3809934 prefixEnd_3809934 1956327403907001849403439 := by
  unfold tailWord_3809934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17369963622408409721079607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92639805986178185179091237 17369963622408409721079607)
  ·
    refine ⟨26054945433612614581619411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17369963622408409721079607 26054945433612614581619411)
    ·
      refine ⟨39082418150418921872429117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26054945433612614581619411 39082418150418921872429117)
      ·
        refine ⟨14655906806407095702160919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39082418150418921872429117 14655906806407095702160919)
        ·
          refine ⟨21983860209610643553241379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655906806407095702160919 21983860209610643553241379)
          ·
            refine ⟨32975790314415965329862069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983860209610643553241379 32975790314415965329862069)
            ·
              refine ⟨3091480341976496749674569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32975790314415965329862069 3091480341976496749674569)
              ·
                refine ⟨2318610256482372562255927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3091480341976496749674569 2318610256482372562255927)
                ·
                  refine ⟨3477915384723558843383891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318610256482372562255927 3477915384723558843383891)
                  ·
                    refine ⟨5216873077085338265075837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3477915384723558843383891 5216873077085338265075837)
                    ·
                      refine ⟨1956327403907001849403439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216873077085338265075837 1956327403907001849403439)
                      ·
                        rfl

theorem cell23_3809934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3809934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809934 prefixEnd_3809934 := by exact prefixLift 3809934
  have htrace : WordTrace (prefixWord ++ tailWord_3809934) baseStart_3809934 baseEnd_3809934 := by
    simpa [prefixWord, tailWord_3809934, baseEnd_3809934] using wordTrace_append hprefix tailTrace_3809934
  have hstable : (prefixWord ++ tailWord_3809934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809934).length < 2 ^ (prefixWord ++ tailWord_3809934).sum := by decide
  have hdescent : baseEnd_3809934 < baseStart_3809934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809943 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3809943 : Nat := 118140960795 + 3809943 * 2 ^ 59
def prefixEnd_3809943 : Nat := 4983230072969 + 3 ^ 40 * 3809943 * 2
def baseEnd_3809943 : Nat := 1956332025232892314190897

theorem tailTrace_3809943 : CollatzResearch.WordTrace tailWord_3809943 prefixEnd_3809943 1956332025232892314190897 := by
  unfold tailWord_3809943
  simp only [CollatzResearch.WordTrace]
  refine ⟨138960037236234672305714483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92640024824156448203809655 138960037236234672305714483)
  ·
    refine ⟨208440055854352008458571725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138960037236234672305714483 208440055854352008458571725)
    ·
      refine ⟨78165020945382003171964397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208440055854352008458571725 78165020945382003171964397)
      ·
        refine ⟨29311882854518251189486649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78165020945382003171964397 29311882854518251189486649)
        ·
          refine ⟨21983912140888688392114987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29311882854518251189486649 21983912140888688392114987)
          ·
            refine ⟨32975868211333032588172481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983912140888688392114987 32975868211333032588172481)
            ·
              refine ⟨24731901158499774441129361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32975868211333032588172481 24731901158499774441129361)
              ·
                refine ⟨18548925868874830830847021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24731901158499774441129361 18548925868874830830847021)
                ·
                  refine ⟨6955847200828061561567633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18548925868874830830847021 6955847200828061561567633)
                  ·
                    refine ⟨5216885400621046171175725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6955847200828061561567633 5216885400621046171175725)
                    ·
                      refine ⟨1956332025232892314190897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216885400621046171175725 1956332025232892314190897)
                      ·
                        rfl

theorem cell23_3809943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3809943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809943 prefixEnd_3809943 := by exact prefixLift 3809943
  have htrace : WordTrace (prefixWord ++ tailWord_3809943) baseStart_3809943 baseEnd_3809943 := by
    simpa [prefixWord, tailWord_3809943, baseEnd_3809943] using wordTrace_append hprefix tailTrace_3809943
  have hstable : (prefixWord ++ tailWord_3809943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809943).length < 2 ^ (prefixWord ++ tailWord_3809943).sum := by decide
  have hdescent : baseEnd_3809943 < baseStart_3809943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809985 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3809985 : Nat := 118140960795 + 3809985 * 2 ^ 59
def prefixEnd_3809985 : Nat := 4983230072969 + 3 ^ 40 * 3809985 * 2
def baseEnd_3809985 : Nat := 1956353591420381149865705

theorem tailTrace_3809985 : CollatzResearch.WordTrace tailWord_3809985 prefixEnd_3809985 1956353591420381149865705 := by
  unfold tailWord_3809985
  simp only [CollatzResearch.WordTrace]
  refine ⟨138961569102082513478743409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92641046068055008985828939 138961569102082513478743409)
  ·
    refine ⟨104221176826561885109057557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138961569102082513478743409 104221176826561885109057557)
    ·
      refine ⟨4885367663745088364487073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104221176826561885109057557 4885367663745088364487073)
      ·
        refine ⟨3664025747808816273365305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4885367663745088364487073 3664025747808816273365305)
        ·
          refine ⟨2748019310856612205023979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664025747808816273365305 2748019310856612205023979)
          ·
            refine ⟨4122028966284918307535969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748019310856612205023979 4122028966284918307535969)
            ·
              refine ⟨3091521724713688730651977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122028966284918307535969 3091521724713688730651977)
              ·
                refine ⟨2318641293535266547988983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3091521724713688730651977 2318641293535266547988983)
                ·
                  refine ⟨3477961940302899821983475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318641293535266547988983 3477961940302899821983475)
                  ·
                    refine ⟨5216942910454349732975213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3477961940302899821983475 5216942910454349732975213)
                    ·
                      refine ⟨1956353591420381149865705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5216942910454349732975213 1956353591420381149865705)
                      ·
                        rfl

theorem cell23_3809985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3809985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809985 prefixEnd_3809985 := by exact prefixLift 3809985
  have htrace : WordTrace (prefixWord ++ tailWord_3809985) baseStart_3809985 baseEnd_3809985 := by
    simpa [prefixWord, tailWord_3809985, baseEnd_3809985] using wordTrace_append hprefix tailTrace_3809985
  have hstable : (prefixWord ++ tailWord_3809985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809985).length < 2 ^ (prefixWord ++ tailWord_3809985).sum := by decide
  have hdescent : baseEnd_3809985 < baseStart_3809985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809997 : List Nat := [1, 6, 2, 1, 2, 2, 1, 8]
def baseStart_3809997 : Nat := 118140960795 + 3809997 * 2 ^ 59
def prefixEnd_3809997 : Nat := 4983230072969 + 3 ^ 40 * 3809997 * 2
def baseEnd_3809997 : Nat := 72457768636601300107987

theorem tailTrace_3809997 : CollatzResearch.WordTrace tailWord_3809997 prefixEnd_3809997 72457768636601300107987 := by
  unfold tailWord_3809997
  simp only [CollatzResearch.WordTrace]
  refine ⟨138962006778039039528180245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92641337852026026352120163 138962006778039039528180245)
  ·
    refine ⟨6513844067720579977883449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138962006778039039528180245 6513844067720579977883449)
    ·
      refine ⟨4885383050790434983412587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6513844067720579977883449 4885383050790434983412587)
      ·
        refine ⟨7328074576185652475118881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885383050790434983412587 7328074576185652475118881)
        ·
          refine ⟨5496055932139239356339161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7328074576185652475118881 5496055932139239356339161)
          ·
            refine ⟨4122041949104429517254371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496055932139239356339161 4122041949104429517254371)
            ·
              refine ⟨6183062923656644275881557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122041949104429517254371 6183062923656644275881557)
              ·
                refine ⟨72457768636601300107987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6183062923656644275881557 72457768636601300107987)
                ·
                  rfl

theorem cell23_3809997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 8].length) (baseStart_3809997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3809997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3809997 prefixEnd_3809997 := by exact prefixLift 3809997
  have htrace : WordTrace (prefixWord ++ tailWord_3809997) baseStart_3809997 baseEnd_3809997 := by
    simpa [prefixWord, tailWord_3809997, baseEnd_3809997] using wordTrace_append hprefix tailTrace_3809997
  have hstable : (prefixWord ++ tailWord_3809997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809997).length < 2 ^ (prefixWord ++ tailWord_3809997).sum := by decide
  have hdescent : baseEnd_3809997 < baseStart_3809997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810034 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3810034 : Nat := 118140960795 + 3810034 * 2 ^ 59
def prefixEnd_3810034 : Nat := 4983230072969 + 3 ^ 40 * 3810034 * 2
def baseEnd_3810034 : Nat := 1956378751972451458152979

theorem tailTrace_3810034 : CollatzResearch.WordTrace tailWord_3810034 prefixEnd_3810034 1956378751972451458152979 := by
  unfold tailWord_3810034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34740839069726248711819289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92642237519269996564851437 34740839069726248711819289)
  ·
    refine ⟨26055629302294686533864467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34740839069726248711819289 26055629302294686533864467)
    ·
      refine ⟨39083443953442029800796701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26055629302294686533864467 39083443953442029800796701)
      ·
        refine ⟨14656291482540761175298763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39083443953442029800796701 14656291482540761175298763)
        ·
          refine ⟨21984437223811141762948145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14656291482540761175298763 21984437223811141762948145)
          ·
            refine ⟨16488327917858356322211109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21984437223811141762948145 16488327917858356322211109)
            ·
              refine ⟨3091561484598441810414583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16488327917858356322211109 3091561484598441810414583)
              ·
                refine ⟨4637342226897662715621875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091561484598441810414583 4637342226897662715621875)
                ·
                  refine ⟨6956013340346494073432813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637342226897662715621875 6956013340346494073432813)
                  ·
                    refine ⟨2608505002629935277537305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6956013340346494073432813 2608505002629935277537305)
                    ·
                      refine ⟨1956378751972451458152979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608505002629935277537305 1956378751972451458152979)
                      ·
                        rfl

theorem cell23_3810034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3810034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810034 prefixEnd_3810034 := by exact prefixLift 3810034
  have htrace : WordTrace (prefixWord ++ tailWord_3810034) baseStart_3810034 baseEnd_3810034 := by
    simpa [prefixWord, tailWord_3810034, baseEnd_3810034] using wordTrace_append hprefix tailTrace_3810034
  have hstable : (prefixWord ++ tailWord_3810034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810034).length < 2 ^ (prefixWord ++ tailWord_3810034).sum := by decide
  have hdescent : baseEnd_3810034 < baseStart_3810034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810063 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_3810063 : Nat := 118140960795 + 3810063 * 2 ^ 59
def prefixEnd_3810063 : Nat := 4983230072969 + 3 ^ 40 * 3810063 * 2
def baseEnd_3810063 : Nat := 1956393642911431844690345

theorem tailTrace_3810063 : CollatzResearch.WordTrace tailWord_3810063 prefixEnd_3810063 1956393642911431844690345 := by
  unfold tailWord_3810063
  simp only [CollatzResearch.WordTrace]
  refine ⟨138964413995799932800082843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92642942663866621866721895 138964413995799932800082843)
  ·
    refine ⟨208446620993699899200124265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138964413995799932800082843 208446620993699899200124265)
    ·
      refine ⟨156334965745274924400093199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208446620993699899200124265 156334965745274924400093199)
      ·
        refine ⟨234502448617912386600139799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156334965745274924400093199 234502448617912386600139799)
        ·
          refine ⟨351753672926868579900209699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234502448617912386600139799 351753672926868579900209699)
          ·
            refine ⟨527630509390302869850314549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351753672926868579900209699 527630509390302869850314549)
            ·
              refine ⟨49465360255340894048466989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527630509390302869850314549 49465360255340894048466989)
              ·
                refine ⟨18549510095752835268175121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49465360255340894048466989 18549510095752835268175121)
                ·
                  refine ⟨13912132571814626451131341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18549510095752835268175121 13912132571814626451131341)
                  ·
                    refine ⟨5217049714430484919174253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13912132571814626451131341 5217049714430484919174253)
                    ·
                      refine ⟨1956393642911431844690345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217049714430484919174253 1956393642911431844690345)
                      ·
                        rfl

theorem cell23_3810063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_3810063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810063 prefixEnd_3810063 := by exact prefixLift 3810063
  have htrace : WordTrace (prefixWord ++ tailWord_3810063) baseStart_3810063 baseEnd_3810063 := by
    simpa [prefixWord, tailWord_3810063, baseEnd_3810063] using wordTrace_append hprefix tailTrace_3810063
  have hstable : (prefixWord ++ tailWord_3810063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810063).length < 2 ^ (prefixWord ++ tailWord_3810063).sum := by decide
  have hdescent : baseEnd_3810063 < baseStart_3810063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810083 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 2, 5]
def baseStart_3810083 : Nat := 118140960795 + 3810083 * 2 ^ 59
def prefixEnd_3810083 : Nat := 4983230072969 + 3 ^ 40 * 3810083 * 2
def baseEnd_3810083 : Nat := 652134637508173922146751

theorem tailTrace_3810083 : CollatzResearch.WordTrace tailWord_3810083 prefixEnd_3810083 652134637508173922146751 := by
  unfold tailWord_3810083
  simp only [CollatzResearch.WordTrace]
  refine ⟨138965143455727476215810903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92643428970484984143873935 138965143455727476215810903)
  ·
    refine ⟨208447715183591214323716355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138965143455727476215810903 208447715183591214323716355)
    ·
      refine ⟨312671572775386821485574533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208447715183591214323716355 312671572775386821485574533)
      ·
        refine ⟨58625919895385029028545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312671572775386821485574533 58625919895385029028545225)
        ·
          refine ⟨43969439921538771771408919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58625919895385029028545225 43969439921538771771408919)
          ·
            refine ⟨65954159882308157657113379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43969439921538771771408919 65954159882308157657113379)
            ·
              refine ⟨98931239823462236485670069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65954159882308157657113379 98931239823462236485670069)
              ·
                refine ⟨9274803733449584670531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98931239823462236485670069 9274803733449584670531569)
                ·
                  refine ⟨6956102800087188502898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9274803733449584670531569 6956102800087188502898677)
                  ·
                    refine ⟨652134637508173922146751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6956102800087188502898677 652134637508173922146751)
                    ·
                      rfl

theorem cell23_3810083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 5].length) (baseStart_3810083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810083 prefixEnd_3810083 := by exact prefixLift 3810083
  have htrace : WordTrace (prefixWord ++ tailWord_3810083) baseStart_3810083 baseEnd_3810083 := by
    simpa [prefixWord, tailWord_3810083, baseEnd_3810083] using wordTrace_append hprefix tailTrace_3810083
  have hstable : (prefixWord ++ tailWord_3810083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810083).length < 2 ^ (prefixWord ++ tailWord_3810083).sum := by decide
  have hdescent : baseEnd_3810083 < baseStart_3810083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810120 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_3810120 : Nat := 118140960795 + 3810120 * 2 ^ 59
def prefixEnd_3810120 : Nat := 4983230072969 + 3 ^ 40 * 3810120 * 2
def baseEnd_3810120 : Nat := 1956422911308738121677583

theorem tailTrace_3810120 : CollatzResearch.WordTrace tailWord_3810120 prefixEnd_3810120 1956422911308738121677583 := by
  unfold tailWord_3810120
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483246478296715767453907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92644328637728954356605209 69483246478296715767453907)
  ·
    refine ⟨104224869717445073651180861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69483246478296715767453907 104224869717445073651180861)
    ·
      refine ⟨39084326144041902619192823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104224869717445073651180861 39084326144041902619192823)
      ·
        refine ⟨58626489216062853928789235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39084326144041902619192823 58626489216062853928789235)
        ·
          refine ⟨87939733824094280893183853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58626489216062853928789235 87939733824094280893183853)
          ·
            refine ⟨32977400184035355334943945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87939733824094280893183853 32977400184035355334943945)
            ·
              refine ⟨24733050138026516501207959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32977400184035355334943945 24733050138026516501207959)
              ·
                refine ⟨37099575207039774751811939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24733050138026516501207959 37099575207039774751811939)
                ·
                  refine ⟨55649362810559662127717909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37099575207039774751811939 55649362810559662127717909)
                  ·
                    refine ⟨2608563881744984162236777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55649362810559662127717909 2608563881744984162236777)
                    ·
                      refine ⟨1956422911308738121677583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608563881744984162236777 1956422911308738121677583)
                      ·
                        rfl

theorem cell23_3810120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_3810120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810120 prefixEnd_3810120 := by exact prefixLift 3810120
  have htrace : WordTrace (prefixWord ++ tailWord_3810120) baseStart_3810120 baseEnd_3810120 := by
    simpa [prefixWord, tailWord_3810120, baseEnd_3810120] using wordTrace_append hprefix tailTrace_3810120
  have hstable : (prefixWord ++ tailWord_3810120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810120).length < 2 ^ (prefixWord ++ tailWord_3810120).sum := by decide
  have hdescent : baseEnd_3810120 < baseStart_3810120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810130 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3810130 : Nat := 118140960795 + 3810130 * 2 ^ 59
def prefixEnd_3810130 : Nat := 4983230072969 + 3 ^ 40 * 3810130 * 2
def baseEnd_3810130 : Nat := 652142682038427694184179

theorem tailTrace_3810130 : CollatzResearch.WordTrace tailWord_3810130 prefixEnd_3810130 652142682038427694184179 := by
  unfold tailWord_3810130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34741714421639300810692961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92644571791038135495181229 34741714421639300810692961)
  ·
    refine ⟨26056285816229475608019721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34741714421639300810692961 26056285816229475608019721)
    ·
      refine ⟨19542214362172106706014791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26056285816229475608019721 19542214362172106706014791)
      ·
        refine ⟨29313321543258160059022187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19542214362172106706014791 29313321543258160059022187)
        ·
          refine ⟨43969982314887240088533281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29313321543258160059022187 43969982314887240088533281)
          ·
            refine ⟨32977486736165430066399961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43969982314887240088533281 32977486736165430066399961)
            ·
              refine ⟨24733115052124072549799971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32977486736165430066399961 24733115052124072549799971)
              ·
                refine ⟨37099672578186108824699957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24733115052124072549799971 37099672578186108824699957)
                ·
                  refine ⟨3478094304204947702315621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37099672578186108824699957 3478094304204947702315621)
                  ·
                    refine ⟨652142682038427694184179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478094304204947702315621 652142682038427694184179)
                    ·
                      rfl

theorem cell23_3810130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3810130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810130 prefixEnd_3810130 := by exact prefixLift 3810130
  have htrace : WordTrace (prefixWord ++ tailWord_3810130) baseStart_3810130 baseEnd_3810130 := by
    simpa [prefixWord, tailWord_3810130, baseEnd_3810130] using wordTrace_append hprefix tailTrace_3810130
  have hstable : (prefixWord ++ tailWord_3810130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810130).length < 2 ^ (prefixWord ++ tailWord_3810130).sum := by decide
  have hdescent : baseEnd_3810130 < baseStart_3810130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810197 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_3810197 : Nat := 118140960795 + 3810197 * 2 ^ 59
def prefixEnd_3810197 : Nat := 4983230072969 + 3 ^ 40 * 3810197 * 2
def baseEnd_3810197 : Nat := 1956462449319134320414729

theorem tailTrace_3810197 : CollatzResearch.WordTrace tailWord_3810197 prefixEnd_3810197 1956462449319134320414729 := by
  unfold tailWord_3810197
  simp only [CollatzResearch.WordTrace]
  refine ⟨138969301377314473685460845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92646200918209649123640563 138969301377314473685460845)
  ·
    refine ⟨52113488016492927632047817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138969301377314473685460845 52113488016492927632047817)
    ·
      refine ⟨39085116012369695724035863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52113488016492927632047817 39085116012369695724035863)
      ·
        refine ⟨58627674018554543586053795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39085116012369695724035863 58627674018554543586053795)
        ·
          refine ⟨87941511027831815379080693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58627674018554543586053795 87941511027831815379080693)
          ·
            refine ⟨8244516658859232691788815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87941511027831815379080693 8244516658859232691788815)
            ·
              refine ⟨12366774988288849037683223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244516658859232691788815 12366774988288849037683223)
              ·
                refine ⟨18550162482433273556524835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366774988288849037683223 18550162482433273556524835)
                ·
                  refine ⟨27825243723649910334787253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18550162482433273556524835 27825243723649910334787253)
                  ·
                    refine ⟨2608616599092179093886305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27825243723649910334787253 2608616599092179093886305)
                    ·
                      refine ⟨1956462449319134320414729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608616599092179093886305 1956462449319134320414729)
                      ·
                        rfl

theorem cell23_3810197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_3810197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810197 prefixEnd_3810197 := by exact prefixLift 3810197
  have htrace : WordTrace (prefixWord ++ tailWord_3810197) baseStart_3810197 baseEnd_3810197 := by
    simpa [prefixWord, tailWord_3810197, baseEnd_3810197] using wordTrace_append hprefix tailTrace_3810197
  have hstable : (prefixWord ++ tailWord_3810197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810197).length < 2 ^ (prefixWord ++ tailWord_3810197).sum := by decide
  have hdescent : baseEnd_3810197 < baseStart_3810197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810198 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3810198 : Nat := 118140960795 + 3810198 * 2 ^ 59
def prefixEnd_3810198 : Nat := 4983230072969 + 3 ^ 40 * 3810198 * 2
def baseEnd_3810198 : Nat := 652154320933262938834075

theorem tailTrace_3810198 : CollatzResearch.WordTrace tailWord_3810198 prefixEnd_3810198 652154320933262938834075 := by
  unfold tailWord_3810198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685583615644428178515453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92646225233540567237498165 8685583615644428178515453)
  ·
    refine ⟨3257093855866660566943295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8685583615644428178515453 3257093855866660566943295)
    ·
      refine ⟨4885640783799990850414943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257093855866660566943295 4885640783799990850414943)
      ·
        refine ⟨7328461175699986275622415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885640783799990850414943 7328461175699986275622415)
        ·
          refine ⟨10992691763549979413433623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328461175699986275622415 10992691763549979413433623)
          ·
            refine ⟨16489037645324969120150435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10992691763549979413433623 16489037645324969120150435)
            ·
              refine ⟨24733556467987453680225653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489037645324969120150435 24733556467987453680225653)
              ·
                refine ⟨2318770918873823782521155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24733556467987453680225653 2318770918873823782521155)
                ·
                  refine ⟨3478156378310735673781733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318770918873823782521155 3478156378310735673781733)
                  ·
                    refine ⟨652154320933262938834075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478156378310735673781733 652154320933262938834075)
                    ·
                      rfl

theorem cell23_3810198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3810198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810198 prefixEnd_3810198 := by exact prefixLift 3810198
  have htrace : WordTrace (prefixWord ++ tailWord_3810198) baseStart_3810198 baseEnd_3810198 := by
    simpa [prefixWord, tailWord_3810198, baseEnd_3810198] using wordTrace_append hprefix tailTrace_3810198
  have hstable : (prefixWord ++ tailWord_3810198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810198).length < 2 ^ (prefixWord ++ tailWord_3810198).sum := by decide
  have hdescent : baseEnd_3810198 < baseStart_3810198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810207 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 1, 5]
def baseStart_3810207 : Nat := 118140960795 + 3810207 * 2 ^ 59
def prefixEnd_3810207 : Nat := 4983230072969 + 3 ^ 40 * 3810207 * 2
def baseEnd_3810207 : Nat := 652155861375226427096561

theorem tailTrace_3810207 : CollatzResearch.WordTrace tailWord_3810207 prefixEnd_3810207 652155861375226427096561 := by
  unfold tailWord_3810207
  simp only [CollatzResearch.WordTrace]
  refine ⟨138969666107278245393324875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92646444071518830262216583 138969666107278245393324875)
  ·
    refine ⟨208454499160917368089987313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138969666107278245393324875 208454499160917368089987313)
    ·
      refine ⟨156340874370688026067490485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208454499160917368089987313 156340874370688026067490485)
      ·
        refine ⟨14656956972252002443827233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156340874370688026067490485 14656956972252002443827233)
        ·
          refine ⟨10992717729189001832870425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14656956972252002443827233 10992717729189001832870425)
          ·
            refine ⟨8244538296891751374652819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992717729189001832870425 8244538296891751374652819)
            ·
              refine ⟨12366807445337627061979229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244538296891751374652819 12366807445337627061979229)
              ·
                refine ⟨4637552792001610148242211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12366807445337627061979229 4637552792001610148242211)
                ·
                  refine ⟨6956329188002415222363317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637552792001610148242211 6956329188002415222363317)
                  ·
                    refine ⟨652155861375226427096561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6956329188002415222363317 652155861375226427096561)
                    ·
                      rfl

theorem cell23_3810207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_3810207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810207 prefixEnd_3810207 := by exact prefixLift 3810207
  have htrace : WordTrace (prefixWord ++ tailWord_3810207) baseStart_3810207 baseEnd_3810207 := by
    simpa [prefixWord, tailWord_3810207, baseEnd_3810207] using wordTrace_append hprefix tailTrace_3810207
  have hstable : (prefixWord ++ tailWord_3810207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810207).length < 2 ^ (prefixWord ++ tailWord_3810207).sum := by decide
  have hdescent : baseEnd_3810207 < baseStart_3810207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810220 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_3810220 : Nat := 118140960795 + 3810220 * 2 ^ 59
def prefixEnd_3810220 : Nat := 4983230072969 + 3 ^ 40 * 3810220 * 2
def baseEnd_3810220 : Nat := 652158086458062576809041

theorem tailTrace_3810220 : CollatzResearch.WordTrace tailWord_3810220 prefixEnd_3810220 652158086458062576809041 := by
  unfold tailWord_3810220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69485070128115574306774057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92646760170820765742365409 69485070128115574306774057)
  ·
    refine ⟨52113802596086680730080543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69485070128115574306774057 52113802596086680730080543)
    ·
      refine ⟨78170703894130021095120815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52113802596086680730080543 78170703894130021095120815)
      ·
        refine ⟨117256055841195031642681223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78170703894130021095120815 117256055841195031642681223)
        ·
          refine ⟨175884083761792547464021835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117256055841195031642681223 175884083761792547464021835)
          ·
            refine ⟨263826125642688821196032753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175884083761792547464021835 263826125642688821196032753)
            ·
              refine ⟨197869594232016615897024565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263826125642688821196032753 197869594232016615897024565)
              ·
                refine ⟨18550274459251557740346053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197869594232016615897024565 18550274459251557740346053)
                ·
                  refine ⟨3478176461109667076314885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18550274459251557740346053 3478176461109667076314885)
                  ·
                    refine ⟨652158086458062576809041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478176461109667076314885 652158086458062576809041)
                    ·
                      rfl

theorem cell23_3810220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_3810220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810220 prefixEnd_3810220 := by exact prefixLift 3810220
  have htrace : WordTrace (prefixWord ++ tailWord_3810220) baseStart_3810220 baseEnd_3810220 := by
    simpa [prefixWord, tailWord_3810220, baseEnd_3810220] using wordTrace_append hprefix tailTrace_3810220
  have hstable : (prefixWord ++ tailWord_3810220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810220).length < 2 ^ (prefixWord ++ tailWord_3810220).sum := by decide
  have hdescent : baseEnd_3810220 < baseStart_3810220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810240 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_3810240 : Nat := 118140960795 + 3810240 * 2 ^ 59
def prefixEnd_3810240 : Nat := 4983230072969 + 3 ^ 40 * 3810240 * 2
def baseEnd_3810240 : Nat := 1956484528987277652177031

theorem tailTrace_3810240 : CollatzResearch.WordTrace tailWord_3810240 prefixEnd_3810240 1956484528987277652177031 := by
  unfold tailWord_3810240
  simp only [CollatzResearch.WordTrace]
  refine ⟨69485434858079346014638087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92647246477439128019517449 69485434858079346014638087)
  ·
    refine ⟨104228152287119019021957131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69485434858079346014638087 104228152287119019021957131)
    ·
      refine ⟨156342228430678528532935697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104228152287119019021957131 156342228430678528532935697)
      ·
        refine ⟨117256671323008896399701773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156342228430678528532935697 117256671323008896399701773)
        ·
          refine ⟨43971251746128336149888165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117256671323008896399701773 43971251746128336149888165)
          ·
            refine ⟨8244609702399063028104031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43971251746128336149888165 8244609702399063028104031)
            ·
              refine ⟨12366914553598594542156047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244609702399063028104031 12366914553598594542156047)
              ·
                refine ⟨18550371830397891813234071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366914553598594542156047 18550371830397891813234071)
                ·
                  refine ⟨27825557745596837719851107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18550371830397891813234071 27825557745596837719851107)
                  ·
                    refine ⟨41738336618395256579776661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27825557745596837719851107 41738336618395256579776661)
                    ·
                      refine ⟨1956484528987277652177031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41738336618395256579776661 1956484528987277652177031)
                      ·
                        rfl

theorem cell23_3810240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_3810240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810240 prefixEnd_3810240 := by exact prefixLift 3810240
  have htrace : WordTrace (prefixWord ++ tailWord_3810240) baseStart_3810240 baseEnd_3810240 := by
    simpa [prefixWord, tailWord_3810240, baseEnd_3810240] using wordTrace_append hprefix tailTrace_3810240
  have hstable : (prefixWord ++ tailWord_3810240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810240).length < 2 ^ (prefixWord ++ tailWord_3810240).sum := by decide
  have hdescent : baseEnd_3810240 < baseStart_3810240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810243 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_3810243 : Nat := 118140960795 + 3810243 * 2 ^ 59
def prefixEnd_3810243 : Nat := 4983230072969 + 3 ^ 40 * 3810243 * 2
def baseEnd_3810243 : Nat := 1956486069429241140439517

theorem tailTrace_3810243 : CollatzResearch.WordTrace tailWord_3810243 prefixEnd_3810243 1956486069429241140439517 := by
  unfold tailWord_3810243
  simp only [CollatzResearch.WordTrace]
  refine ⟨138970979135147823541635383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92647319423431882361090255 138970979135147823541635383)
  ·
    refine ⟨208456468702721735312453075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138970979135147823541635383 208456468702721735312453075)
    ·
      refine ⟨312684703054082602968679613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208456468702721735312453075 312684703054082602968679613)
      ·
        refine ⟨117256763645280976113254855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312684703054082602968679613 117256763645280976113254855)
        ·
          refine ⟨175885145467921464169882283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117256763645280976113254855 175885145467921464169882283)
          ·
            refine ⟨263827718201882196254823425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175885145467921464169882283 263827718201882196254823425)
            ·
              refine ⟨197870788651411647191117569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263827718201882196254823425 197870788651411647191117569)
              ·
                refine ⟨148403091488558735393338177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197870788651411647191117569 148403091488558735393338177)
                ·
                  refine ⟨111302318616419051545003633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148403091488558735393338177 111302318616419051545003633)
                  ·
                    refine ⟨83476738962314288658752725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111302318616419051545003633 83476738962314288658752725)
                    ·
                      refine ⟨1956486069429241140439517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83476738962314288658752725 1956486069429241140439517)
                      ·
                        rfl

theorem cell23_3810243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_3810243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810243 prefixEnd_3810243 := by exact prefixLift 3810243
  have htrace : WordTrace (prefixWord ++ tailWord_3810243) baseStart_3810243 baseEnd_3810243 := by
    simpa [prefixWord, tailWord_3810243, baseEnd_3810243] using wordTrace_append hprefix tailTrace_3810243
  have hstable : (prefixWord ++ tailWord_3810243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810243).length < 2 ^ (prefixWord ++ tailWord_3810243).sum := by decide
  have hdescent : baseEnd_3810243 < baseStart_3810243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810247 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_3810247 : Nat := 118140960795 + 3810247 * 2 ^ 59
def prefixEnd_3810247 : Nat := 4983230072969 + 3 ^ 40 * 3810247 * 2
def baseEnd_3810247 : Nat := 1956488123351859124789499

theorem tailTrace_3810247 : CollatzResearch.WordTrace tailWord_3810247 prefixEnd_3810247 1956488123351859124789499 := by
  unfold tailWord_3810247
  simp only [CollatzResearch.WordTrace]
  refine ⟨138971125027133332224780995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92647416684755554816520663 138971125027133332224780995)
  ·
    refine ⟨208456687540699998337171493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138971125027133332224780995 208456687540699998337171493)
    ·
      refine ⟨39085628913881249688219655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208456687540699998337171493 39085628913881249688219655)
      ·
        refine ⟨58628443370821874532329483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39085628913881249688219655 58628443370821874532329483)
        ·
          refine ⟨87942665056232811798494225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58628443370821874532329483 87942665056232811798494225)
          ·
            refine ⟨65956998792174608848870669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87942665056232811798494225 65956998792174608848870669)
            ·
              refine ⟨24733874547065478318326501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65956998792174608848870669 24733874547065478318326501)
              ·
                refine ⟨4637601477574777184686219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24733874547065478318326501 4637601477574777184686219)
                ·
                  refine ⟨6956402216362165777029329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637601477574777184686219 6956402216362165777029329)
                  ·
                    refine ⟨5217301662271624332771997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956402216362165777029329 5217301662271624332771997)
                    ·
                      refine ⟨1956488123351859124789499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217301662271624332771997 1956488123351859124789499)
                      ·
                        rfl

theorem cell23_3810247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_3810247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810247 prefixEnd_3810247 := by exact prefixLift 3810247
  have htrace : WordTrace (prefixWord ++ tailWord_3810247) baseStart_3810247 baseEnd_3810247 := by
    simpa [prefixWord, tailWord_3810247, baseEnd_3810247] using wordTrace_append hprefix tailTrace_3810247
  have hstable : (prefixWord ++ tailWord_3810247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810247).length < 2 ^ (prefixWord ++ tailWord_3810247).sum := by decide
  have hdescent : baseEnd_3810247 < baseStart_3810247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810292 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3810292 : Nat := 118140960795 + 3810292 * 2 ^ 59
def prefixEnd_3810292 : Nat := 4983230072969 + 3 ^ 40 * 3810292 * 2
def baseEnd_3810292 : Nat := 652170409993770482908931

theorem tailTrace_3810292 : CollatzResearch.WordTrace tailWord_3810292 prefixEnd_3810292 652170409993770482908931 := by
  unfold tailWord_3810292
  simp only [CollatzResearch.WordTrace]
  refine ⟨69486383155985152455084565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92648510874646869940112753 69486383155985152455084565)
  ·
    refine ⟨3257174210436804021332089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69486383155985152455084565 3257174210436804021332089)
    ·
      refine ⟨2442880657827603015999067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3257174210436804021332089 2442880657827603015999067)
      ·
        refine ⟨3664320986741404523998601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442880657827603015999067 3664320986741404523998601)
        ·
          refine ⟨2748240740056053392998951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664320986741404523998601 2748240740056053392998951)
          ·
            refine ⟨4122361110084080089498427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748240740056053392998951 4122361110084080089498427)
            ·
              refine ⟨6183541665126120134247641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122361110084080089498427 6183541665126120134247641)
              ·
                refine ⟨4637656248844590100685731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183541665126120134247641 4637656248844590100685731)
                ·
                  refine ⟨6956484373266885151028597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637656248844590100685731 6956484373266885151028597)
                  ·
                    refine ⟨652170409993770482908931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6956484373266885151028597 652170409993770482908931)
                    ·
                      rfl

theorem cell23_3810292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3810292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810292 prefixEnd_3810292 := by exact prefixLift 3810292
  have htrace : WordTrace (prefixWord ++ tailWord_3810292) baseStart_3810292 baseEnd_3810292 := by
    simpa [prefixWord, tailWord_3810292, baseEnd_3810292] using wordTrace_append hprefix tailTrace_3810292
  have hstable : (prefixWord ++ tailWord_3810292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810292).length < 2 ^ (prefixWord ++ tailWord_3810292).sum := by decide
  have hdescent : baseEnd_3810292 < baseStart_3810292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810320 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_3810320 : Nat := 118140960795 + 3810320 * 2 ^ 59
def prefixEnd_3810320 : Nat := 4983230072969 + 3 ^ 40 * 3810320 * 2
def baseEnd_3810320 : Nat := 1956525607439637339176663

theorem tailTrace_3810320 : CollatzResearch.WordTrace tailWord_3810320 prefixEnd_3810320 1956525607439637339176663 := by
  unfold tailWord_3810320
  simp only [CollatzResearch.WordTrace]
  refine ⟨69486893777934432846094207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92649191703912577128125609 69486893777934432846094207)
  ·
    refine ⟨104230340666901649269141311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69486893777934432846094207 104230340666901649269141311)
    ·
      refine ⟨156345511000352473903711967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104230340666901649269141311 156345511000352473903711967)
      ·
        refine ⟨234518266500528710855567951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156345511000352473903711967 234518266500528710855567951)
        ·
          refine ⟨351777399750793066283351927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234518266500528710855567951 351777399750793066283351927)
          ·
            refine ⟨527666099626189599425027891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351777399750793066283351927 527666099626189599425027891)
            ·
              refine ⟨791499149439284399137541837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527666099626189599425027891 791499149439284399137541837)
              ·
                refine ⟨296812181039731649676578189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 791499149439284399137541837 296812181039731649676578189)
                ·
                  refine ⟨111304567889899368628716821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296812181039731649676578189 111304567889899368628716821)
                  ·
                    refine ⟨5217401619839032904471101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111304567889899368628716821 5217401619839032904471101)
                    ·
                      refine ⟨1956525607439637339176663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217401619839032904471101 1956525607439637339176663)
                      ·
                        rfl

theorem cell23_3810320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_3810320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810320 prefixEnd_3810320 := by exact prefixLift 3810320
  have htrace : WordTrace (prefixWord ++ tailWord_3810320) baseStart_3810320 baseEnd_3810320 := by
    simpa [prefixWord, tailWord_3810320, baseEnd_3810320] using wordTrace_append hprefix tailTrace_3810320
  have hstable : (prefixWord ++ tailWord_3810320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810320).length < 2 ^ (prefixWord ++ tailWord_3810320).sum := by decide
  have hdescent : baseEnd_3810320 < baseStart_3810320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810337 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3810337 : Nat := 118140960795 + 3810337 * 2 ^ 59
def prefixEnd_3810337 : Nat := 4983230072969 + 3 ^ 40 * 3810337 * 2
def baseEnd_3810337 : Nat := 1956534336610763772664085

theorem tailTrace_3810337 : CollatzResearch.WordTrace tailWord_3810337 prefixEnd_3810337 1956534336610763772664085 := by
  unfold tailWord_3810337
  simp only [CollatzResearch.WordTrace]
  refine ⟨138974407596807277595557265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92649605064538185063704843 138974407596807277595557265)
  ·
    refine ⟨104230805697605458196667949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138974407596807277595557265 104230805697605458196667949)
    ·
      refine ⟨39086552136602046823750481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104230805697605458196667949 39086552136602046823750481)
      ·
        refine ⟨29314914102451535117812861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39086552136602046823750481 29314914102451535117812861)
        ·
          refine ⟨10993092788419325669179823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29314914102451535117812861 10993092788419325669179823)
          ·
            refine ⟨16489639182628988503769735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993092788419325669179823 16489639182628988503769735)
            ·
              refine ⟨24734458773943482755654603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489639182628988503769735 24734458773943482755654603)
              ·
                refine ⟨37101688160915224133481905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24734458773943482755654603 37101688160915224133481905)
                ·
                  refine ⟨27826266120686418100111429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37101688160915224133481905 27826266120686418100111429)
                  ·
                    refine ⟨5217424897628703393770893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27826266120686418100111429 5217424897628703393770893)
                    ·
                      refine ⟨1956534336610763772664085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217424897628703393770893 1956534336610763772664085)
                      ·
                        rfl

theorem cell23_3810337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3810337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810337 prefixEnd_3810337 := by exact prefixLift 3810337
  have htrace : WordTrace (prefixWord ++ tailWord_3810337) baseStart_3810337 baseEnd_3810337 := by
    simpa [prefixWord, tailWord_3810337, baseEnd_3810337] using wordTrace_append hprefix tailTrace_3810337
  have hstable : (prefixWord ++ tailWord_3810337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810337).length < 2 ^ (prefixWord ++ tailWord_3810337).sum := by decide
  have hdescent : baseEnd_3810337 < baseStart_3810337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810377 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 7, 2]
def baseStart_3810377 : Nat := 118140960795 + 3810377 * 2 ^ 59
def prefixEnd_3810377 : Nat := 4983230072969 + 3 ^ 40 * 3810377 * 2
def baseEnd_3810377 : Nat := 1956554875836943616163901

theorem tailTrace_3810377 : CollatzResearch.WordTrace tailWord_3810377 prefixEnd_3810377 1956554875836943616163901 := by
  unfold tailWord_3810377
  simp only [CollatzResearch.WordTrace]
  refine ⟨138975866516662364427013385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92650577677774909618008923 138975866516662364427013385)
  ·
    refine ⟨104231899887496773320260039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138975866516662364427013385 104231899887496773320260039)
    ·
      refine ⟨156347849831245159980390059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104231899887496773320260039 156347849831245159980390059)
      ·
        refine ⟨234521774746867739970585089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156347849831245159980390059 234521774746867739970585089)
        ·
          refine ⟨175891331060150804977938817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234521774746867739970585089 175891331060150804977938817)
          ·
            refine ⟨131918498295113103733454113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175891331060150804977938817 131918498295113103733454113)
            ·
              refine ⟨98938873721334827800090585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131918498295113103733454113 98938873721334827800090585)
              ·
                refine ⟨74204155291001120850067939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98938873721334827800090585 74204155291001120850067939)
                ·
                  refine ⟨111306232936501681275101909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74204155291001120850067939 111306232936501681275101909)
                  ·
                    refine ⟨2608739834449258154885201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 111306232936501681275101909 2608739834449258154885201)
                    ·
                      refine ⟨1956554875836943616163901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608739834449258154885201 1956554875836943616163901)
                      ·
                        rfl

theorem cell23_3810377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 7, 2].length) (baseStart_3810377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810377 prefixEnd_3810377 := by exact prefixLift 3810377
  have htrace : WordTrace (prefixWord ++ tailWord_3810377) baseStart_3810377 baseEnd_3810377 := by
    simpa [prefixWord, tailWord_3810377, baseEnd_3810377] using wordTrace_append hprefix tailTrace_3810377
  have hstable : (prefixWord ++ tailWord_3810377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810377).length < 2 ^ (prefixWord ++ tailWord_3810377).sum := by decide
  have hdescent : baseEnd_3810377 < baseStart_3810377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810407 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3810407 : Nat := 118140960795 + 3810407 * 2 ^ 59
def prefixEnd_3810407 : Nat := 4983230072969 + 3 ^ 40 * 3810407 * 2
def baseEnd_3810407 : Nat := 1956570280256578498788763

theorem tailTrace_3810407 : CollatzResearch.WordTrace tailWord_3810407 prefixEnd_3810407 1956570280256578498788763 := by
  unfold tailWord_3810407
  simp only [CollatzResearch.WordTrace]
  refine ⟨138976960706553679550605475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92651307137702453033736983 138976960706553679550605475)
  ·
    refine ⟨208465441059830519325908213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138976960706553679550605475 208465441059830519325908213)
    ·
      refine ⟨19543635099359111186803895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208465441059830519325908213 19543635099359111186803895)
      ·
        refine ⟨29315452649038666780205843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543635099359111186803895 29315452649038666780205843)
        ·
          refine ⟨43973178973558000170308765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29315452649038666780205843 43973178973558000170308765)
          ·
            refine ⟨16489942115084250063865787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43973178973558000170308765 16489942115084250063865787)
            ·
              refine ⟨24734913172626375095798681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489942115084250063865787 24734913172626375095798681)
              ·
                refine ⟨18551184879469781321849011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24734913172626375095798681 18551184879469781321849011)
                ·
                  refine ⟨27826777319204671982773517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18551184879469781321849011 27826777319204671982773517)
                  ·
                    refine ⟨10435041494701751993540069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27826777319204671982773517 10435041494701751993540069)
                    ·
                      refine ⟨1956570280256578498788763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10435041494701751993540069 1956570280256578498788763)
                      ·
                        rfl

theorem cell23_3810407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3810407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810407 prefixEnd_3810407 := by exact prefixLift 3810407
  have htrace : WordTrace (prefixWord ++ tailWord_3810407) baseStart_3810407 baseEnd_3810407 := by
    simpa [prefixWord, tailWord_3810407, baseEnd_3810407] using wordTrace_append hprefix tailTrace_3810407
  have hstable : (prefixWord ++ tailWord_3810407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810407).length < 2 ^ (prefixWord ++ tailWord_3810407).sum := by decide
  have hdescent : baseEnd_3810407 < baseStart_3810407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810417 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_3810417 : Nat := 118140960795 + 3810417 * 2 ^ 59
def prefixEnd_3810417 : Nat := 4983230072969 + 3 ^ 40 * 3810417 * 2
def baseEnd_3810417 : Nat := 652191805021041153221239

theorem tailTrace_3810417 : CollatzResearch.WordTrace tailWord_3810417 prefixEnd_3810417 652191805021041153221239 := by
  unfold tailWord_3810417
  simp only [CollatzResearch.WordTrace]
  refine ⟨138977325436517451258469505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92651550291011634172313003 138977325436517451258469505)
  ·
    refine ⟨104232994077388088443852129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138977325436517451258469505 104232994077388088443852129)
    ·
      refine ⟨78174745558041066332889097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104232994077388088443852129 78174745558041066332889097)
      ·
        refine ⟨58631059168530799749666823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78174745558041066332889097 58631059168530799749666823)
        ·
          refine ⟨87946588752796199624500235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58631059168530799749666823 87946588752796199624500235)
          ·
            refine ⟨131919883129194299436750353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87946588752796199624500235 131919883129194299436750353)
            ·
              refine ⟨98939912346895724577562765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131919883129194299436750353 98939912346895724577562765)
              ·
                refine ⟨37102467130085896716586037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98939912346895724577562765 37102467130085896716586037)
                ·
                  refine ⟨3478356293445552817179941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37102467130085896716586037 3478356293445552817179941)
                  ·
                    refine ⟨652191805021041153221239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478356293445552817179941 652191805021041153221239)
                    ·
                      rfl

theorem cell23_3810417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_3810417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810417 prefixEnd_3810417 := by exact prefixLift 3810417
  have htrace : WordTrace (prefixWord ++ tailWord_3810417) baseStart_3810417 baseEnd_3810417 := by
    simpa [prefixWord, tailWord_3810417, baseEnd_3810417] using wordTrace_append hprefix tailTrace_3810417
  have hstable : (prefixWord ++ tailWord_3810417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810417).length < 2 ^ (prefixWord ++ tailWord_3810417).sum := by decide
  have hdescent : baseEnd_3810417 < baseStart_3810417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810427 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3]
def baseStart_3810427 : Nat := 118140960795 + 3810427 * 2 ^ 59
def prefixEnd_3810427 : Nat := 4983230072969 + 3 ^ 40 * 3810427 * 2
def baseEnd_3810427 : Nat := 1956580549869668420538671

theorem tailTrace_3810427 : CollatzResearch.WordTrace tailWord_3810427 prefixEnd_3810427 1956580549869668420538671 := by
  unfold tailWord_3810427
  simp only [CollatzResearch.WordTrace]
  refine ⟨138977690166481222966333535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92651793444320815310889023 138977690166481222966333535)
  ·
    refine ⟨208466535249721834449500303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138977690166481222966333535 208466535249721834449500303)
    ·
      refine ⟨312699802874582751674250455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208466535249721834449500303 312699802874582751674250455)
      ·
        refine ⟨469049704311874127511375683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312699802874582751674250455 469049704311874127511375683)
        ·
          refine ⟨703574556467811191267063525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469049704311874127511375683 703574556467811191267063525)
          ·
            refine ⟨131920229337714598362574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 703574556467811191267063525 131920229337714598362574411)
            ·
              refine ⟨197880344006571897543861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131920229337714598362574411 197880344006571897543861617)
              ·
                refine ⟨148410258004928923157896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197880344006571897543861617 148410258004928923157896213)
                ·
                  refine ⟨6956730843981043273026385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148410258004928923157896213 6956730843981043273026385)
                  ·
                    refine ⟨5217548132985782454769789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6956730843981043273026385 5217548132985782454769789)
                    ·
                      refine ⟨1956580549869668420538671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217548132985782454769789 1956580549869668420538671)
                      ·
                        rfl

theorem cell23_3810427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 3].length) (baseStart_3810427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810427 prefixEnd_3810427 := by exact prefixLift 3810427
  have htrace : WordTrace (prefixWord ++ tailWord_3810427) baseStart_3810427 baseEnd_3810427 := by
    simpa [prefixWord, tailWord_3810427, baseEnd_3810427] using wordTrace_append hprefix tailTrace_3810427
  have hstable : (prefixWord ++ tailWord_3810427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810427).length < 2 ^ (prefixWord ++ tailWord_3810427).sum := by decide
  have hdescent : baseEnd_3810427 < baseStart_3810427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810514 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3810514 : Nat := 118140960795 + 3810514 * 2 ^ 59
def prefixEnd_3810514 : Nat := 4983230072969 + 3 ^ 40 * 3810514 * 2
def baseEnd_3810514 : Nat := 1956625222686609580150771

theorem tailTrace_3810514 : CollatzResearch.WordTrace tailWord_3810514 prefixEnd_3810514 1956625222686609580150771 := by
  unfold tailWord_3810514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34745215829291509206187649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92653908878110691216500397 34745215829291509206187649)
  ·
    refine ⟨26058911871968631904640737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34745215829291509206187649 26058911871968631904640737)
    ·
      refine ⟨19544183903976473928480553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26058911871968631904640737 19544183903976473928480553)
      ·
        refine ⟨14658137927982355446360415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19544183903976473928480553 14658137927982355446360415)
        ·
          refine ⟨21987206891973533169540623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658137927982355446360415 21987206891973533169540623)
          ·
            refine ⟨32980810337960299754310935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987206891973533169540623 32980810337960299754310935)
            ·
              refine ⟨49471215506940449631466403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32980810337960299754310935 49471215506940449631466403)
              ·
                refine ⟨74206823260410674447199605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49471215506940449631466403 74206823260410674447199605)
                ·
                  refine ⟨6956889680663500729424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74206823260410674447199605 6956889680663500729424963)
                  ·
                    refine ⟨10435334520995251094137445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6956889680663500729424963 10435334520995251094137445)
                    ·
                      refine ⟨1956625222686609580150771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10435334520995251094137445 1956625222686609580150771)
                      ·
                        rfl

theorem cell23_3810514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3810514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810514 prefixEnd_3810514 := by exact prefixLift 3810514
  have htrace : WordTrace (prefixWord ++ tailWord_3810514) baseStart_3810514 baseEnd_3810514 := by
    simpa [prefixWord, tailWord_3810514, baseEnd_3810514] using wordTrace_append hprefix tailTrace_3810514
  have hstable : (prefixWord ++ tailWord_3810514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810514).length < 2 ^ (prefixWord ++ tailWord_3810514).sum := by decide
  have hdescent : baseEnd_3810514 < baseStart_3810514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810527 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3810527 : Nat := 118140960795 + 3810527 * 2 ^ 59
def prefixEnd_3810527 : Nat := 4983230072969 + 3 ^ 40 * 3810527 * 2
def baseEnd_3810527 : Nat := 1956631897935118029288211

theorem tailTrace_3810527 : CollatzResearch.WordTrace tailWord_3810527 prefixEnd_3810527 1956631897935118029288211 := by
  unfold tailWord_3810527
  simp only [CollatzResearch.WordTrace]
  refine ⟨138981337466118940044973835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92654224977412626696649223 138981337466118940044973835)
  ·
    refine ⟨208472006199178410067460753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138981337466118940044973835 208472006199178410067460753)
    ·
      refine ⟨156354004649383807550595565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208472006199178410067460753 156354004649383807550595565)
      ·
        refine ⟨58632751743518927831473337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156354004649383807550595565 58632751743518927831473337)
        ·
          refine ⟨43974563807639195873605003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58632751743518927831473337 43974563807639195873605003)
          ·
            refine ⟨65961845711458793810407505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43974563807639195873605003 65961845711458793810407505)
            ·
              refine ⟨49471384283594095357805629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65961845711458793810407505 49471384283594095357805629)
              ·
                refine ⟨18551769106347785759177111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49471384283594095357805629 18551769106347785759177111)
                ·
                  refine ⟨27827653659521678638765667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18551769106347785759177111 27827653659521678638765667)
                  ·
                    refine ⟨41741480489282517958148501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27827653659521678638765667 41741480489282517958148501)
                    ·
                      refine ⟨1956631897935118029288211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41741480489282517958148501 1956631897935118029288211)
                      ·
                        rfl

theorem cell23_3810527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3810527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810527 prefixEnd_3810527 := by exact prefixLift 3810527
  have htrace : WordTrace (prefixWord ++ tailWord_3810527) baseStart_3810527 baseEnd_3810527 := by
    simpa [prefixWord, tailWord_3810527, baseEnd_3810527] using wordTrace_append hprefix tailTrace_3810527
  have hstable : (prefixWord ++ tailWord_3810527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810527).length < 2 ^ (prefixWord ++ tailWord_3810527).sum := by decide
  have hdescent : baseEnd_3810527 < baseStart_3810527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810535 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3810535 : Nat := 118140960795 + 3810535 * 2 ^ 59
def prefixEnd_3810535 : Nat := 4983230072969 + 3 ^ 40 * 3810535 * 2
def baseEnd_3810535 : Nat := 1956636005780353997988175

theorem tailTrace_3810535 : CollatzResearch.WordTrace tailWord_3810535 prefixEnd_3810535 1956636005780353997988175 := by
  unfold tailWord_3810535
  simp only [CollatzResearch.WordTrace]
  refine ⟨138981629250089957411265059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92654419500059971607510039 138981629250089957411265059)
  ·
    refine ⟨208472443875134936116897589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138981629250089957411265059 208472443875134936116897589)
    ·
      refine ⟨19544291613293900260959149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208472443875134936116897589 19544291613293900260959149)
      ·
        refine ⟨7329109354985212597859681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19544291613293900260959149 7329109354985212597859681)
        ·
          refine ⟨5496832016238909448394761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7329109354985212597859681 5496832016238909448394761)
          ·
            refine ⟨4122624012179182086296071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496832016238909448394761 4122624012179182086296071)
            ·
              refine ⟨6183936018268773129444107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122624012179182086296071 6183936018268773129444107)
              ·
                refine ⟨9275904027403159694166161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6183936018268773129444107 9275904027403159694166161)
                ·
                  refine ⟨6956928020552369770624621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9275904027403159694166161 6956928020552369770624621)
                  ·
                    refine ⟨2608848007707138663984233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6956928020552369770624621 2608848007707138663984233)
                    ·
                      refine ⟨1956636005780353997988175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608848007707138663984233 1956636005780353997988175)
                      ·
                        rfl

theorem cell23_3810535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3810535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810535 prefixEnd_3810535 := by exact prefixLift 3810535
  have htrace : WordTrace (prefixWord ++ tailWord_3810535) baseStart_3810535 baseEnd_3810535 := by
    simpa [prefixWord, tailWord_3810535, baseEnd_3810535] using wordTrace_append hprefix tailTrace_3810535
  have hstable : (prefixWord ++ tailWord_3810535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810535).length < 2 ^ (prefixWord ++ tailWord_3810535).sum := by decide
  have hdescent : baseEnd_3810535 < baseStart_3810535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810557 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3810557 : Nat := 118140960795 + 3810557 * 2 ^ 59
def prefixEnd_3810557 : Nat := 4983230072969 + 3 ^ 40 * 3810557 * 2
def baseEnd_3810557 : Nat := 1956647302354752911913073

theorem tailTrace_3810557 : CollatzResearch.WordTrace tailWord_3810557 prefixEnd_3810557 1956647302354752911913073 := by
  unfold tailWord_3810557
  simp only [CollatzResearch.WordTrace]
  refine ⟨138982431656010255168565925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92654954437340170112377283 138982431656010255168565925)
  ·
    refine ⟨26059205935501922844106111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138982431656010255168565925 26059205935501922844106111)
    ·
      refine ⟨39088808903252884266159167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26059205935501922844106111 39088808903252884266159167)
      ·
        refine ⟨58633213354879326399238751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39088808903252884266159167 58633213354879326399238751)
        ·
          refine ⟨87949820032318989598858127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58633213354879326399238751 87949820032318989598858127)
          ·
            refine ⟨131924730048478484398287191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87949820032318989598858127 131924730048478484398287191)
            ·
              refine ⟨197887095072717726597430787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131924730048478484398287191 197887095072717726597430787)
              ·
                refine ⟨296830642609076589896146181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197887095072717726597430787 296830642609076589896146181)
                ·
                  refine ⟨55655745489201860605527409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296830642609076589896146181 55655745489201860605527409)
                  ·
                    refine ⟨41741809116901395454145557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55655745489201860605527409 41741809116901395454145557)
                    ·
                      refine ⟨1956647302354752911913073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41741809116901395454145557 1956647302354752911913073)
                      ·
                        rfl

theorem cell23_3810557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3810557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810557 prefixEnd_3810557 := by exact prefixLift 3810557
  have htrace : WordTrace (prefixWord ++ tailWord_3810557) baseStart_3810557 baseEnd_3810557 := by
    simpa [prefixWord, tailWord_3810557, baseEnd_3810557] using wordTrace_append hprefix tailTrace_3810557
  have hstable : (prefixWord ++ tailWord_3810557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810557).length < 2 ^ (prefixWord ++ tailWord_3810557).sum := by decide
  have hdescent : baseEnd_3810557 < baseStart_3810557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810558 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3810558 : Nat := 118140960795 + 3810558 * 2 ^ 59
def prefixEnd_3810558 : Nat := 4983230072969 + 3 ^ 40 * 3810558 * 2
def baseEnd_3810558 : Nat := 652215938611802469333523

theorem tailTrace_3810558 : CollatzResearch.WordTrace tailWord_3810558 prefixEnd_3810558 652215938611802469333523 := by
  unfold tailWord_3810558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372808516125829042419041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92654978752671088226234885 17372808516125829042419041)
  ·
    refine ⟨13029606387094371781814281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17372808516125829042419041 13029606387094371781814281)
    ·
      refine ⟨9772204790320778836360711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029606387094371781814281 9772204790320778836360711)
      ·
        refine ⟨14658307185481168254541067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772204790320778836360711 14658307185481168254541067)
        ·
          refine ⟨21987460778221752381811601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658307185481168254541067 21987460778221752381811601)
          ·
            refine ⟨16490595583666314286358701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21987460778221752381811601 16490595583666314286358701)
            ·
              refine ⟨6183973343874867857384513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16490595583666314286358701 6183973343874867857384513)
              ·
                refine ⟨4637980007906150893038385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183973343874867857384513 4637980007906150893038385)
                ·
                  refine ⟨3478485005929613169778789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637980007906150893038385 3478485005929613169778789)
                  ·
                    refine ⟨652215938611802469333523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478485005929613169778789 652215938611802469333523)
                    ·
                      rfl

theorem cell23_3810558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3810558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810558 prefixEnd_3810558 := by exact prefixLift 3810558
  have htrace : WordTrace (prefixWord ++ tailWord_3810558) baseStart_3810558 baseEnd_3810558 := by
    simpa [prefixWord, tailWord_3810558, baseEnd_3810558] using wordTrace_append hprefix tailTrace_3810558
  have hstable : (prefixWord ++ tailWord_3810558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810558).length < 2 ^ (prefixWord ++ tailWord_3810558).sum := by decide
  have hdescent : baseEnd_3810558 < baseStart_3810558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810578 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3810578 : Nat := 118140960795 + 3810578 * 2 ^ 59
def prefixEnd_3810578 : Nat := 4983230072969 + 3 ^ 40 * 3810578 * 2
def baseEnd_3810578 : Nat := 1956658085448497329750477

theorem tailTrace_3810578 : CollatzResearch.WordTrace tailWord_3810578 prefixEnd_3810578 1956658085448497329750477 := by
  unfold tailWord_3810578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34745799397233543938770097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92655465059289450503386925 34745799397233543938770097)
  ·
    refine ⟨26059349547925157954077573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34745799397233543938770097 26059349547925157954077573)
    ·
      refine ⟨4886128040235967116389545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26059349547925157954077573 4886128040235967116389545)
      ·
        refine ⟨3664596030176975337292159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886128040235967116389545 3664596030176975337292159)
        ·
          refine ⟨5496894045265463005938239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664596030176975337292159 5496894045265463005938239)
          ·
            refine ⟨8245341067898194508907359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496894045265463005938239 8245341067898194508907359)
            ·
              refine ⟨12368011601847291763361039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245341067898194508907359 12368011601847291763361039)
              ·
                refine ⟨18552017402770937645041559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12368011601847291763361039 18552017402770937645041559)
                ·
                  refine ⟨27828026104156406467562339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18552017402770937645041559 27828026104156406467562339)
                  ·
                    refine ⟨41742039156234609701343509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27828026104156406467562339 41742039156234609701343509)
                    ·
                      refine ⟨1956658085448497329750477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41742039156234609701343509 1956658085448497329750477)
                      ·
                        rfl

theorem cell23_3810578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3810578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810578 prefixEnd_3810578 := by exact prefixLift 3810578
  have htrace : WordTrace (prefixWord ++ tailWord_3810578) baseStart_3810578 baseEnd_3810578 := by
    simpa [prefixWord, tailWord_3810578, baseEnd_3810578] using wordTrace_append hprefix tailTrace_3810578
  have hstable : (prefixWord ++ tailWord_3810578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810578).length < 2 ^ (prefixWord ++ tailWord_3810578).sum := by decide
  have hdescent : baseEnd_3810578 < baseStart_3810578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810624 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_3810624 : Nat := 118140960795 + 3810624 * 2 ^ 59
def prefixEnd_3810624 : Nat := 4983230072969 + 3 ^ 40 * 3810624 * 2
def baseEnd_3810624 : Nat := 1956681705558604149775265

theorem tailTrace_3810624 : CollatzResearch.WordTrace tailWord_3810624 prefixEnd_3810624 1956681705558604149775265 := by
  unfold tailWord_3810624
  simp only [CollatzResearch.WordTrace]
  refine ⟨69492437673383762805627463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92656583564511683740836617 69492437673383762805627463)
  ·
    refine ⟨104238656510075644208441195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69492437673383762805627463 104238656510075644208441195)
    ·
      refine ⟨156357984765113466312661793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104238656510075644208441195 156357984765113466312661793)
      ·
        refine ⟨117268488573835099734496345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156357984765113466312661793 117268488573835099734496345)
        ·
          refine ⟨87951366430376324800872259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117268488573835099734496345 87951366430376324800872259)
          ·
            refine ⟨131927049645564487201308389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87951366430376324800872259 131927049645564487201308389)
            ·
              refine ⟨24736321808543341350245323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131927049645564487201308389 24736321808543341350245323)
              ·
                refine ⟨37104482712815012025367985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24736321808543341350245323 37104482712815012025367985)
                ·
                  refine ⟨27828362034611259019025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37104482712815012025367985 27828362034611259019025989)
                  ·
                    refine ⟨5217817881489611066067373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27828362034611259019025989 5217817881489611066067373)
                    ·
                      refine ⟨1956681705558604149775265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5217817881489611066067373 1956681705558604149775265)
                      ·
                        rfl

theorem cell23_3810624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_3810624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810624 prefixEnd_3810624 := by exact prefixLift 3810624
  have htrace : WordTrace (prefixWord ++ tailWord_3810624) baseStart_3810624 baseEnd_3810624 := by
    simpa [prefixWord, tailWord_3810624, baseEnd_3810624] using wordTrace_append hprefix tailTrace_3810624
  have hstable : (prefixWord ++ tailWord_3810624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810624).length < 2 ^ (prefixWord ++ tailWord_3810624).sum := by decide
  have hdescent : baseEnd_3810624 < baseStart_3810624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810634 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_3810634 : Nat := 118140960795 + 3810634 * 2 ^ 59
def prefixEnd_3810634 : Nat := 4983230072969 + 3 ^ 40 * 3810634 * 2
def baseEnd_3810634 : Nat := 1956686840365149110650219

theorem tailTrace_3810634 : CollatzResearch.WordTrace tailWord_3810634 prefixEnd_3810634 1956686840365149110650219 := by
  unfold tailWord_3810634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34746310019182824329779739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92656826717820864879412637 34746310019182824329779739)
  ·
    refine ⟨52119465028774236494669609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34746310019182824329779739 52119465028774236494669609)
    ·
      refine ⟨39089598771580677371002207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52119465028774236494669609 39089598771580677371002207)
      ·
        refine ⟨58634398157371016056503311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39089598771580677371002207 58634398157371016056503311)
        ·
          refine ⟨87951597236056524084754967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58634398157371016056503311 87951597236056524084754967)
          ·
            refine ⟨131927395854084786127132451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87951597236056524084754967 131927395854084786127132451)
            ·
              refine ⟨197891093781127179190698677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131927395854084786127132451 197891093781127179190698677)
              ·
                refine ⟨18552290041980673049128001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197891093781127179190698677 18552290041980673049128001)
                ·
                  refine ⟨13914217531485504786846001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18552290041980673049128001 13914217531485504786846001)
                  ·
                    refine ⟨10435663148614128590134501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13914217531485504786846001 10435663148614128590134501)
                    ·
                      refine ⟨1956686840365149110650219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10435663148614128590134501 1956686840365149110650219)
                      ·
                        rfl

theorem cell23_3810634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_3810634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810634 prefixEnd_3810634 := by exact prefixLift 3810634
  have htrace : WordTrace (prefixWord ++ tailWord_3810634) baseStart_3810634 baseEnd_3810634 := by
    simpa [prefixWord, tailWord_3810634, baseEnd_3810634] using wordTrace_append hprefix tailTrace_3810634
  have hstable : (prefixWord ++ tailWord_3810634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810634).length < 2 ^ (prefixWord ++ tailWord_3810634).sum := by decide
  have hdescent : baseEnd_3810634 < baseStart_3810634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810644 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 9]
def baseStart_3810644 : Nat := 118140960795 + 3810644 * 2 ^ 59
def prefixEnd_3810644 : Nat := 4983230072969 + 3 ^ 40 * 3810644 * 2
def baseEnd_3810644 : Nat := 217410219463521563502797

theorem tailTrace_3810644 : CollatzResearch.WordTrace tailWord_3810644 prefixEnd_3810644 217410219463521563502797 := by
  unfold tailWord_3810644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69492802403347534513491493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92657069871130046017988657 69492802403347534513491493)
  ·
    refine ⟨13029900450627662721279655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69492802403347534513491493 13029900450627662721279655)
    ·
      refine ⟨19544850675941494081919483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13029900450627662721279655 19544850675941494081919483)
      ·
        refine ⟨29317276013912241122879225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19544850675941494081919483 29317276013912241122879225)
        ·
          refine ⟨21987957010434180842159419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29317276013912241122879225 21987957010434180842159419)
          ·
            refine ⟨32981935515651271263239129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21987957010434180842159419 32981935515651271263239129)
            ·
              refine ⟨24736451636738453447429347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32981935515651271263239129 24736451636738453447429347)
              ·
                refine ⟨37104677455107680171144021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24736451636738453447429347 37104677455107680171144021)
                ·
                  refine ⟨217410219463521563502797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37104677455107680171144021 217410219463521563502797)
                  ·
                    rfl

theorem cell23_3810644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_3810644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810644 prefixEnd_3810644 := by exact prefixLift 3810644
  have htrace : WordTrace (prefixWord ++ tailWord_3810644) baseStart_3810644 baseEnd_3810644 := by
    simpa [prefixWord, tailWord_3810644, baseEnd_3810644] using wordTrace_append hprefix tailTrace_3810644
  have hstable : (prefixWord ++ tailWord_3810644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810644).length < 2 ^ (prefixWord ++ tailWord_3810644).sum := by decide
  have hdescent : baseEnd_3810644 < baseStart_3810644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810661 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 5]
def baseStart_3810661 : Nat := 118140960795 + 3810661 * 2 ^ 59
def prefixEnd_3810661 : Nat := 4983230072969 + 3 ^ 40 * 3810661 * 2
def baseEnd_3810661 : Nat := 217411189371424500556955

theorem tailTrace_3810661 : CollatzResearch.WordTrace tailWord_3810661 prefixEnd_3810661 217411189371424500556955 := by
  unfold tailWord_3810661
  simp only [CollatzResearch.WordTrace]
  refine ⟨138986224847633480930351837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92657483231755653953567891 138986224847633480930351837)
  ·
    refine ⟨52119834317862555348881939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138986224847633480930351837 52119834317862555348881939)
    ·
      refine ⟨78179751476793833023322909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52119834317862555348881939 78179751476793833023322909)
      ·
        refine ⟨29317406803797687383746091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78179751476793833023322909 29317406803797687383746091)
        ·
          refine ⟨43976110205696531075619137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29317406803797687383746091 43976110205696531075619137)
          ·
            refine ⟨32982082654272398306714353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43976110205696531075619137 32982082654272398306714353)
            ·
              refine ⟨24736561990704298730035765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32982082654272398306714353 24736561990704298730035765)
              ·
                refine ⟨2319052686628528005940853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24736561990704298730035765 2319052686628528005940853)
                ·
                  refine ⟨217411189371424500556955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2319052686628528005940853 217411189371424500556955)
                  ·
                    rfl

theorem cell23_3810661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_3810661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810661 prefixEnd_3810661 := by exact prefixLift 3810661
  have htrace : WordTrace (prefixWord ++ tailWord_3810661) baseStart_3810661 baseEnd_3810661 := by
    simpa [prefixWord, tailWord_3810661, baseEnd_3810661] using wordTrace_append hprefix tailTrace_3810661
  have hstable : (prefixWord ++ tailWord_3810661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810661).length < 2 ^ (prefixWord ++ tailWord_3810661).sum := by decide
  have hdescent : baseEnd_3810661 < baseStart_3810661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810681 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 5, 2]
def baseStart_3810681 : Nat := 118140960795 + 3810681 * 2 ^ 59
def prefixEnd_3810681 : Nat := 4983230072969 + 3 ^ 40 * 3810681 * 2
def baseEnd_3810681 : Nat := 1956710973955910426762503

theorem tailTrace_3810681 : CollatzResearch.WordTrace tailWord_3810681 prefixEnd_3810681 1956710973955910426762503 := by
  unfold tailWord_3810681
  simp only [CollatzResearch.WordTrace]
  refine ⟨138986954307561024346079897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92657969538374016230719931 138986954307561024346079897)
  ·
    refine ⟨104240215730670768259559923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138986954307561024346079897 104240215730670768259559923)
    ·
      refine ⟨156360323596006152389339885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104240215730670768259559923 156360323596006152389339885)
      ·
        refine ⟨58635121348502307146002457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156360323596006152389339885 58635121348502307146002457)
        ·
          refine ⟨43976341011376730359501843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58635121348502307146002457 43976341011376730359501843)
          ·
            refine ⟨65964511517065095539252765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43976341011376730359501843 65964511517065095539252765)
            ·
              refine ⟨24736691818899410827219787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65964511517065095539252765 24736691818899410827219787)
              ·
                refine ⟨37105037728349116240829681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24736691818899410827219787 37105037728349116240829681)
                ·
                  refine ⟨27828778296261837180622261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37105037728349116240829681 27828778296261837180622261)
                  ·
                    refine ⟨2608947965274547235683337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27828778296261837180622261 2608947965274547235683337)
                    ·
                      refine ⟨1956710973955910426762503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608947965274547235683337 1956710973955910426762503)
                      ·
                        rfl

theorem cell23_3810681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_3810681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810681 prefixEnd_3810681 := by exact prefixLift 3810681
  have htrace : WordTrace (prefixWord ++ tailWord_3810681) baseStart_3810681 baseEnd_3810681 := by
    simpa [prefixWord, tailWord_3810681, baseEnd_3810681] using wordTrace_append hprefix tailTrace_3810681
  have hstable : (prefixWord ++ tailWord_3810681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810681).length < 2 ^ (prefixWord ++ tailWord_3810681).sum := by decide
  have hdescent : baseEnd_3810681 < baseStart_3810681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810684 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3810684 : Nat := 118140960795 + 3810684 * 2 ^ 59
def prefixEnd_3810684 : Nat := 4983230072969 + 3 ^ 40 * 3810684 * 2
def baseEnd_3810684 : Nat := 1956712514397873915024989

theorem tailTrace_3810684 : CollatzResearch.WordTrace tailWord_3810684 prefixEnd_3810684 1956712514397873915024989 := by
  unfold tailWord_3810684
  simp only [CollatzResearch.WordTrace]
  refine ⟨69493531863275077929219553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92658042484366770572292737 69493531863275077929219553)
  ·
    refine ⟨52120148897456308446914665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69493531863275077929219553 52120148897456308446914665)
    ·
      refine ⟨39090111673092231335185999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52120148897456308446914665 39090111673092231335185999)
      ·
        refine ⟨58635167509638347002778999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39090111673092231335185999 58635167509638347002778999)
        ·
          refine ⟨87952751264457520504168499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58635167509638347002778999 87952751264457520504168499)
          ·
            refine ⟨131929126896686280756252749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87952751264457520504168499 131929126896686280756252749)
            ·
              refine ⟨49473422586257355283594781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131929126896686280756252749 49473422586257355283594781)
              ·
                refine ⟨18552533469846508231348043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49473422586257355283594781 18552533469846508231348043)
                ·
                  refine ⟨27828800204769762347022065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18552533469846508231348043 27828800204769762347022065)
                  ·
                    refine ⟨20871600153577321760266549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27828800204769762347022065 20871600153577321760266549)
                    ·
                      refine ⟨1956712514397873915024989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20871600153577321760266549 1956712514397873915024989)
                      ·
                        rfl

theorem cell23_3810684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3810684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810684 prefixEnd_3810684 := by exact prefixLift 3810684
  have htrace : WordTrace (prefixWord ++ tailWord_3810684) baseStart_3810684 baseEnd_3810684 := by
    simpa [prefixWord, tailWord_3810684, baseEnd_3810684] using wordTrace_append hprefix tailTrace_3810684
  have hstable : (prefixWord ++ tailWord_3810684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810684).length < 2 ^ (prefixWord ++ tailWord_3810684).sum := by decide
  have hdescent : baseEnd_3810684 < baseStart_3810684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810708 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3810708 : Nat := 118140960795 + 3810708 * 2 ^ 59
def prefixEnd_3810708 : Nat := 4983230072969 + 3 ^ 40 * 3810708 * 2
def baseEnd_3810708 : Nat := 652241612644527273708293

theorem tailTrace_3810708 : CollatzResearch.WordTrace tailWord_3810708 prefixEnd_3810708 652241612644527273708293 := by
  unfold tailWord_3810708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69493969539231603978656389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92658626052308805304875185 69493969539231603978656389)
  ·
    refine ⟨13030119288605925745998073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69493969539231603978656389 13030119288605925745998073)
    ·
      refine ⟨9772589466454444309498555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13030119288605925745998073 9772589466454444309498555)
      ·
        refine ⟨14658884199681666464247833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772589466454444309498555 14658884199681666464247833)
        ·
          refine ⟨10994163149761249848185875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14658884199681666464247833 10994163149761249848185875)
          ·
            refine ⟨16491244724641874772278813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994163149761249848185875 16491244724641874772278813)
            ·
              refine ⟨6184216771740703039604555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16491244724641874772278813 6184216771740703039604555)
              ·
                refine ⟨9276325157611054559406833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184216771740703039604555 9276325157611054559406833)
                ·
                  refine ⟨6957243868208290919555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9276325157611054559406833 6957243868208290919555125)
                  ·
                    refine ⟨652241612644527273708293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6957243868208290919555125 652241612644527273708293)
                    ·
                      rfl

theorem cell23_3810708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3810708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810708 prefixEnd_3810708 := by exact prefixLift 3810708
  have htrace : WordTrace (prefixWord ++ tailWord_3810708) baseStart_3810708 baseEnd_3810708 := by
    simpa [prefixWord, tailWord_3810708, baseEnd_3810708] using wordTrace_append hprefix tailTrace_3810708
  have hstable : (prefixWord ++ tailWord_3810708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810708).length < 2 ^ (prefixWord ++ tailWord_3810708).sum := by decide
  have hdescent : baseEnd_3810708 < baseStart_3810708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810711 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3810711 : Nat := 118140960795 + 3810711 * 2 ^ 59
def prefixEnd_3810711 : Nat := 4983230072969 + 3 ^ 40 * 3810711 * 2
def baseEnd_3810711 : Nat := 1956726378375545309387365

theorem tailTrace_3810711 : CollatzResearch.WordTrace tailWord_3810711 prefixEnd_3810711 1956726378375545309387365 := by
  unfold tailWord_3810711
  simp only [CollatzResearch.WordTrace]
  refine ⟨138988048497452339469671987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92658698998301559646447991 138988048497452339469671987)
  ·
    refine ⟨208482072746178509204507981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138988048497452339469671987 208482072746178509204507981)
    ·
      refine ⟨78180777279816940951690493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208482072746178509204507981 78180777279816940951690493)
      ·
        refine ⟨29317791479931352856883935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78180777279816940951690493 29317791479931352856883935)
        ·
          refine ⟨43976687219897029285325903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29317791479931352856883935 43976687219897029285325903)
          ·
            refine ⟨65965030829845543927988855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43976687219897029285325903 65965030829845543927988855)
            ·
              refine ⟨98947546244768315891983283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65965030829845543927988855 98947546244768315891983283)
              ·
                refine ⟨148421319367152473837974925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98947546244768315891983283 148421319367152473837974925)
                ·
                  refine ⟨55657994762682177689240597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148421319367152473837974925 55657994762682177689240597)
                  ·
                    refine ⟨2608968504500727079183153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55657994762682177689240597 2608968504500727079183153)
                    ·
                      refine ⟨1956726378375545309387365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2608968504500727079183153 1956726378375545309387365)
                      ·
                        rfl

theorem cell23_3810711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3810711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810711 prefixEnd_3810711 := by exact prefixLift 3810711
  have htrace : WordTrace (prefixWord ++ tailWord_3810711) baseStart_3810711 baseEnd_3810711 := by
    simpa [prefixWord, tailWord_3810711, baseEnd_3810711] using wordTrace_append hprefix tailTrace_3810711
  have hstable : (prefixWord ++ tailWord_3810711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810711).length < 2 ^ (prefixWord ++ tailWord_3810711).sum := by decide
  have hdescent : baseEnd_3810711 < baseStart_3810711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810828 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_3810828 : Nat := 118140960795 + 3810828 * 2 ^ 59
def prefixEnd_3810828 : Nat := 4983230072969 + 3 ^ 40 * 3810828 * 2
def baseEnd_3810828 : Nat := 652262151870707117208109

theorem tailTrace_3810828 : CollatzResearch.WordTrace tailWord_3810828 prefixEnd_3810828 652262151870707117208109 := by
  unfold tailWord_3810828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69496157919014234225840569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92661543892018978967787425 69496157919014234225840569)
  ·
    refine ⟨52122118439260675669380427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69496157919014234225840569 52122118439260675669380427)
    ·
      refine ⟨78183177658891013504070641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52122118439260675669380427 78183177658891013504070641)
      ·
        refine ⟨58637383244168260128052981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78183177658891013504070641 58637383244168260128052981)
        ·
          refine ⟨5497254679140774387004967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58637383244168260128052981 5497254679140774387004967)
          ·
            refine ⟨8245882018711161580507451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497254679140774387004967 8245882018711161580507451)
            ·
              refine ⟨12368823028066742370761177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245882018711161580507451 12368823028066742370761177)
              ·
                refine ⟨9276617271050056778070883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12368823028066742370761177 9276617271050056778070883)
                ·
                  refine ⟨13914925906575085167106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9276617271050056778070883 13914925906575085167106325)
                  ·
                    refine ⟨652262151870707117208109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13914925906575085167106325 652262151870707117208109)
                    ·
                      rfl

theorem cell23_3810828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_3810828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810828 prefixEnd_3810828 := by exact prefixLift 3810828
  have htrace : WordTrace (prefixWord ++ tailWord_3810828) baseStart_3810828 baseEnd_3810828 := by
    simpa [prefixWord, tailWord_3810828, baseEnd_3810828] using wordTrace_append hprefix tailTrace_3810828
  have hstable : (prefixWord ++ tailWord_3810828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810828).length < 2 ^ (prefixWord ++ tailWord_3810828).sum := by decide
  have hdescent : baseEnd_3810828 < baseStart_3810828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810835 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 1, 1, 4]
def baseStart_3810835 : Nat := 118140960795 + 3810835 * 2 ^ 59
def prefixEnd_3810835 : Nat := 4983230072969 + 3 ^ 40 * 3810835 * 2
def baseEnd_3810835 : Nat := 1956790049976702824236795

theorem tailTrace_3810835 : CollatzResearch.WordTrace tailWord_3810835 prefixEnd_3810835 1956790049976702824236795 := by
  unfold tailWord_3810835
  simp only [CollatzResearch.WordTrace]
  refine ⟨138992571149003108647185959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92661714099335405764790639 138992571149003108647185959)
  ·
    refine ⟨208488856723504662970778939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138992571149003108647185959 208488856723504662970778939)
    ·
      refine ⟨312733285085256994456168409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208488856723504662970778939 312733285085256994456168409)
      ·
        refine ⟨234549963813942745842126307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312733285085256994456168409 234549963813942745842126307)
        ·
          refine ⟨351824945720914118763189461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234549963813942745842126307 351824945720914118763189461)
          ·
            refine ⟨8245897165333924658512253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 351824945720914118763189461 8245897165333924658512253)
            ·
              refine ⟨3092211437000221746942095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8245897165333924658512253 3092211437000221746942095)
              ·
                refine ⟨4638317155500332620413143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092211437000221746942095 4638317155500332620413143)
                ·
                  refine ⟨6957475733250498930619715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638317155500332620413143 6957475733250498930619715)
                  ·
                    refine ⟨10436213599875748395929573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957475733250498930619715 10436213599875748395929573)
                    ·
                      refine ⟨1956790049976702824236795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10436213599875748395929573 1956790049976702824236795)
                      ·
                        rfl

theorem cell23_3810835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 1, 4].length) (baseStart_3810835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810835 prefixEnd_3810835 := by exact prefixLift 3810835
  have htrace : WordTrace (prefixWord ++ tailWord_3810835) baseStart_3810835 baseEnd_3810835 := by
    simpa [prefixWord, tailWord_3810835, baseEnd_3810835] using wordTrace_append hprefix tailTrace_3810835
  have hstable : (prefixWord ++ tailWord_3810835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810835).length < 2 ^ (prefixWord ++ tailWord_3810835).sum := by decide
  have hdescent : baseEnd_3810835 < baseStart_3810835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810845 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3810845 : Nat := 118140960795 + 3810845 * 2 ^ 59
def prefixEnd_3810845 : Nat := 4983230072969 + 3 ^ 40 * 3810845 * 2
def baseEnd_3810845 : Nat := 652265061594415928370583

theorem tailTrace_3810845 : CollatzResearch.WordTrace tailWord_3810845 prefixEnd_3810845 652265061594415928370583 := by
  unfold tailWord_3810845
  simp only [CollatzResearch.WordTrace]
  refine ⟨138992935878966880355049989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92661957252644586903366659 138992935878966880355049989)
  ·
    refine ⟨26061175477306290066571873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138992935878966880355049989 26061175477306290066571873)
    ·
      refine ⟨19545881607979717549928905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26061175477306290066571873 19545881607979717549928905)
      ·
        refine ⟨14659411205984788162446679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19545881607979717549928905 14659411205984788162446679)
        ·
          refine ⟨21989116808977182243670019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14659411205984788162446679 21989116808977182243670019)
          ·
            refine ⟨32983675213465773365505029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21989116808977182243670019 32983675213465773365505029)
            ·
              refine ⟨6184439102524832506032193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32983675213465773365505029 6184439102524832506032193)
              ·
                refine ⟨4638329326893624379524145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6184439102524832506032193 4638329326893624379524145)
                ·
                  refine ⟨3478746995170218284643109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638329326893624379524145 3478746995170218284643109)
                  ·
                    refine ⟨652265061594415928370583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478746995170218284643109 652265061594415928370583)
                    ·
                      rfl

theorem cell23_3810845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3810845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810845 prefixEnd_3810845 := by exact prefixLift 3810845
  have htrace : WordTrace (prefixWord ++ tailWord_3810845) baseStart_3810845 baseEnd_3810845 := by
    simpa [prefixWord, tailWord_3810845, baseEnd_3810845] using wordTrace_append hprefix tailTrace_3810845
  have hstable : (prefixWord ++ tailWord_3810845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810845).length < 2 ^ (prefixWord ++ tailWord_3810845).sum := by decide
  have hdescent : baseEnd_3810845 < baseStart_3810845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810886 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3810886 : Nat := 118140960795 + 3810886 * 2 ^ 59
def prefixEnd_3810886 : Nat := 4983230072969 + 3 ^ 40 * 3810886 * 2
def baseEnd_3810886 : Nat := 1956816237490082124699061

theorem tailTrace_3810886 : CollatzResearch.WordTrace tailWord_3810886 prefixEnd_3810886 1956816237490082124699061 := by
  unfold tailWord_3810886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343575977244323261165391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92662954181212229571528341 4343575977244323261165391)
  ·
    refine ⟨6515363965866484891748087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4343575977244323261165391 6515363965866484891748087)
    ·
      refine ⟨9773045948799727337622131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515363965866484891748087 9773045948799727337622131)
      ·
        refine ⟨14659568923199591006433197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9773045948799727337622131 14659568923199591006433197)
        ·
          refine ⟨5497338346199846627412449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14659568923199591006433197 5497338346199846627412449)
          ·
            refine ⟨4123003759649884970559337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497338346199846627412449 4123003759649884970559337)
            ·
              refine ⟨3092252819737413727919503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123003759649884970559337 3092252819737413727919503)
              ·
                refine ⟨4638379229606120591879255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092252819737413727919503 4638379229606120591879255)
                ·
                  refine ⟨6957568844409180887818883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638379229606120591879255 6957568844409180887818883)
                  ·
                    refine ⟨10436353266613771331728325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957568844409180887818883 10436353266613771331728325)
                    ·
                      refine ⟨1956816237490082124699061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10436353266613771331728325 1956816237490082124699061)
                      ·
                        rfl

theorem cell23_3810886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3810886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810886 prefixEnd_3810886 := by exact prefixLift 3810886
  have htrace : WordTrace (prefixWord ++ tailWord_3810886) baseStart_3810886 baseEnd_3810886 := by
    simpa [prefixWord, tailWord_3810886, baseEnd_3810886] using wordTrace_append hprefix tailTrace_3810886
  have hstable : (prefixWord ++ tailWord_3810886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810886).length < 2 ^ (prefixWord ++ tailWord_3810886).sum := by decide
  have hdescent : baseEnd_3810886 < baseStart_3810886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810911 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3810911 : Nat := 118140960795 + 3810911 * 2 ^ 59
def prefixEnd_3810911 : Nat := 4983230072969 + 3 ^ 40 * 3810911 * 2
def baseEnd_3810911 : Nat := 1956829074506444526886445

theorem tailTrace_3810911 : CollatzResearch.WordTrace tailWord_3810911 prefixEnd_3810911 1956829074506444526886445 := by
  unfold tailWord_3810911
  simp only [CollatzResearch.WordTrace]
  refine ⟨138995343096727773626952587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92663562064485182417968391 138995343096727773626952587)
  ·
    refine ⟨208493014645091660440428881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138995343096727773626952587 208493014645091660440428881)
    ·
      refine ⟨156369760983818745330321661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208493014645091660440428881 156369760983818745330321661)
      ·
        refine ⟨58638660368932029498870623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156369760983818745330321661 58638660368932029498870623)
        ·
          refine ⟨87957990553398044248305935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58638660368932029498870623 87957990553398044248305935)
          ·
            refine ⟨131936985830097066372458903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87957990553398044248305935 131936985830097066372458903)
            ·
              refine ⟨197905478745145599558688355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131936985830097066372458903 197905478745145599558688355)
              ·
                refine ⟨296858218117718399338032533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197905478745145599558688355 296858218117718399338032533)
                ·
                  refine ⟨13915228974268049968970275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296858218117718399338032533 13915228974268049968970275)
                  ·
                    refine ⟨20872843461402074953455413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13915228974268049968970275 20872843461402074953455413)
                    ·
                      refine ⟨1956829074506444526886445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20872843461402074953455413 1956829074506444526886445)
                      ·
                        rfl

theorem cell23_3810911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3810911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810911 prefixEnd_3810911 := by exact prefixLift 3810911
  have htrace : WordTrace (prefixWord ++ tailWord_3810911) baseStart_3810911 baseEnd_3810911 := by
    simpa [prefixWord, tailWord_3810911, baseEnd_3810911] using wordTrace_append hprefix tailTrace_3810911
  have hstable : (prefixWord ++ tailWord_3810911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810911).length < 2 ^ (prefixWord ++ tailWord_3810911).sum := by decide
  have hdescent : baseEnd_3810911 < baseStart_3810911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810961 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_3810961 : Nat := 118140960795 + 3810961 * 2 ^ 59
def prefixEnd_3810961 : Nat := 4983230072969 + 3 ^ 40 * 3810961 * 2
def baseEnd_3810961 : Nat := 652284916179723110420405

theorem tailTrace_3810961 : CollatzResearch.WordTrace tailWord_3810961 prefixEnd_3810961 652284916179723110420405 := by
  unfold tailWord_3810961
  simp only [CollatzResearch.WordTrace]
  refine ⟨138997166746546632166272737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92664777831031088110848491 138997166746546632166272737)
  ·
    refine ⟨104247875059909974124704553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138997166746546632166272737 104247875059909974124704553)
    ·
      refine ⟨78185906294932480593528415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104247875059909974124704553 78185906294932480593528415)
      ·
        refine ⟨117278859442398720890292623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78185906294932480593528415 117278859442398720890292623)
        ·
          refine ⟨175918289163598081335438935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117278859442398720890292623 175918289163598081335438935)
          ·
            refine ⟨263877433745397122003158403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175918289163598081335438935 263877433745397122003158403)
            ·
              refine ⟨395816150618095683004737605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263877433745397122003158403 395816150618095683004737605)
              ·
                refine ⟨74215528240892940563388301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395816150618095683004737605 74215528240892940563388301)
                ·
                  refine ⟨27830823090334852711270613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74215528240892940563388301 27830823090334852711270613)
                  ·
                    refine ⟨652284916179723110420405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27830823090334852711270613 652284916179723110420405)
                    ·
                      rfl

theorem cell23_3810961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_3810961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810961 prefixEnd_3810961 := by exact prefixLift 3810961
  have htrace : WordTrace (prefixWord ++ tailWord_3810961) baseStart_3810961 baseEnd_3810961 := by
    simpa [prefixWord, tailWord_3810961, baseEnd_3810961] using wordTrace_append hprefix tailTrace_3810961
  have hstable : (prefixWord ++ tailWord_3810961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810961).length < 2 ^ (prefixWord ++ tailWord_3810961).sum := by decide
  have hdescent : baseEnd_3810961 < baseStart_3810961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810976 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2]
def baseStart_3810976 : Nat := 118140960795 + 3810976 * 2 ^ 59
def prefixEnd_3810976 : Nat := 4983230072969 + 3 ^ 40 * 3810976 * 2
def baseEnd_3810976 : Nat := 1956862450748986772573647

theorem tailTrace_3810976 : CollatzResearch.WordTrace tailWord_3810976 prefixEnd_3810976 1956862450748986772573647 := by
  unfold tailWord_3810976
  simp only [CollatzResearch.WordTrace]
  refine ⟨69498856920746144864034391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92665142560994859818712521 69498856920746144864034391)
  ·
    refine ⟨104248285381119217296051587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69498856920746144864034391 104248285381119217296051587)
    ·
      refine ⟨156372428071678825944077381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104248285381119217296051587 156372428071678825944077381)
      ·
        refine ⟨29319830263439779864514509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156372428071678825944077381 29319830263439779864514509)
        ·
          refine ⟨10994936348789917449192941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29319830263439779864514509 10994936348789917449192941)
          ·
            refine ⟨4123101130796219043447353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10994936348789917449192941 4123101130796219043447353)
            ·
              refine ⟨3092325848097164282585515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123101130796219043447353 3092325848097164282585515)
              ·
                refine ⟨4638488772145746423878273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092325848097164282585515 4638488772145746423878273)
                ·
                  refine ⟨3478866579109309817908705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638488772145746423878273 3478866579109309817908705)
                  ·
                    refine ⟨2609149934331982363431529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3478866579109309817908705 2609149934331982363431529)
                    ·
                      refine ⟨1956862450748986772573647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609149934331982363431529 1956862450748986772573647)
                      ·
                        rfl

theorem cell23_3810976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_3810976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3810976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3810976 prefixEnd_3810976 := by exact prefixLift 3810976
  have htrace : WordTrace (prefixWord ++ tailWord_3810976) baseStart_3810976 baseEnd_3810976 := by
    simpa [prefixWord, tailWord_3810976, baseEnd_3810976] using wordTrace_append hprefix tailTrace_3810976
  have hstable : (prefixWord ++ tailWord_3810976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810976).length < 2 ^ (prefixWord ++ tailWord_3810976).sum := by decide
  have hdescent : baseEnd_3810976 < baseStart_3810976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811010 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3811010 : Nat := 118140960795 + 3811010 * 2 ^ 59
def prefixEnd_3811010 : Nat := 4983230072969 + 3 ^ 40 * 3811010 * 2
def baseEnd_3811010 : Nat := 1956879909091239639548491

theorem tailTrace_3811010 : CollatzResearch.WordTrace tailWord_3811010 prefixEnd_3811010 1956879909091239639548491 := by
  unfold tailWord_3811010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34749738480842278383701621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92665969282246075689870989 34749738480842278383701621)
  ·
    refine ⟨3257787982578963598472027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34749738480842278383701621 3257787982578963598472027)
    ·
      refine ⟨4886681973868445397708041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257787982578963598472027 4886681973868445397708041)
      ·
        refine ⟨3665011480401334048281031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886681973868445397708041 3665011480401334048281031)
        ·
          refine ⟨5497517220602001072421547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665011480401334048281031 5497517220602001072421547)
          ·
            refine ⟨8246275830903001608632321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497517220602001072421547 8246275830903001608632321)
            ·
              refine ⟨6184706873177251206474241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246275830903001608632321 6184706873177251206474241)
              ·
                refine ⟨4638530154882938404855681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6184706873177251206474241 4638530154882938404855681)
                ·
                  refine ⟨3478897616162203803641761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638530154882938404855681 3478897616162203803641761)
                  ·
                    refine ⟨2609173212121652852731321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3478897616162203803641761 2609173212121652852731321)
                    ·
                      refine ⟨1956879909091239639548491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609173212121652852731321 1956879909091239639548491)
                      ·
                        rfl

theorem cell23_3811010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3811010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811010 prefixEnd_3811010 := by exact prefixLift 3811010
  have htrace : WordTrace (prefixWord ++ tailWord_3811010) baseStart_3811010 baseEnd_3811010 := by
    simpa [prefixWord, tailWord_3811010, baseEnd_3811010] using wordTrace_append hprefix tailTrace_3811010
  have hstable : (prefixWord ++ tailWord_3811010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811010).length < 2 ^ (prefixWord ++ tailWord_3811010).sum := by decide
  have hdescent : baseEnd_3811010 < baseStart_3811010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811015 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_3811015 : Nat := 118140960795 + 3811015 * 2 ^ 59
def prefixEnd_3811015 : Nat := 4983230072969 + 3 ^ 40 * 3811015 * 2
def baseEnd_3811015 : Nat := 1956882476494512119985967

theorem tailTrace_3811015 : CollatzResearch.WordTrace tailWord_3811015 prefixEnd_3811015 1956882476494512119985967 := by
  unfold tailWord_3811015
  simp only [CollatzResearch.WordTrace]
  refine ⟨138999136288350999388738499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92666090858900666259158999 138999136288350999388738499)
  ·
    refine ⟨208498704432526499083107749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138999136288350999388738499 208498704432526499083107749)
    ·
      refine ⟨39093507081098718578082703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208498704432526499083107749 39093507081098718578082703)
      ·
        refine ⟨58640260621648077867124055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39093507081098718578082703 58640260621648077867124055)
        ·
          refine ⟨87960390932472116800686083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58640260621648077867124055 87960390932472116800686083)
          ·
            refine ⟨131940586398708175201029125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87960390932472116800686083 131940586398708175201029125)
            ·
              refine ⟨24738859949757782850192961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131940586398708175201029125 24738859949757782850192961)
              ·
                refine ⟨18554144962318337137644721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24738859949757782850192961 18554144962318337137644721)
                ·
                  refine ⟨13915608721738752853233541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18554144962318337137644721 13915608721738752853233541)
                  ·
                    refine ⟨2609176635326016159981289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13915608721738752853233541 2609176635326016159981289)
                    ·
                      refine ⟨1956882476494512119985967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609176635326016159981289 1956882476494512119985967)
                      ·
                        rfl

theorem cell23_3811015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_3811015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811015 prefixEnd_3811015 := by exact prefixLift 3811015
  have htrace : WordTrace (prefixWord ++ tailWord_3811015) baseStart_3811015 baseEnd_3811015 := by
    simpa [prefixWord, tailWord_3811015, baseEnd_3811015] using wordTrace_append hprefix tailTrace_3811015
  have hstable : (prefixWord ++ tailWord_3811015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811015).length < 2 ^ (prefixWord ++ tailWord_3811015).sum := by decide
  have hdescent : baseEnd_3811015 < baseStart_3811015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811082 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3811082 : Nat := 118140960795 + 3811082 * 2 ^ 59
def prefixEnd_3811082 : Nat := 4983230072969 + 3 ^ 40 * 3811082 * 2
def baseEnd_3811082 : Nat := 1956916879698363357848159

theorem tailTrace_3811082 : CollatzResearch.WordTrace tailWord_3811082 prefixEnd_3811082 1956916879698363357848159 := by
  unfold tailWord_3811082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750394994777067457856875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92667719986072179887618333 34750394994777067457856875)
  ·
    refine ⟨52125592492165601186785313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34750394994777067457856875 52125592492165601186785313)
    ·
      refine ⟨39094194369124200890088985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52125592492165601186785313 39094194369124200890088985)
      ·
        refine ⟨29320645776843150667566739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39094194369124200890088985 29320645776843150667566739)
        ·
          refine ⟨43980968665264726001350109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29320645776843150667566739 43980968665264726001350109)
          ·
            refine ⟨16492863249474272250506291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43980968665264726001350109 16492863249474272250506291)
            ·
              refine ⟨24739294874211408375759437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16492863249474272250506291 24739294874211408375759437)
              ·
                refine ⟨9277235577829278140909789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24739294874211408375759437 9277235577829278140909789)
                ·
                  refine ⟨3478963341685979302841171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9277235577829278140909789 3478963341685979302841171)
                  ·
                    refine ⟨5218445012528968954261757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3478963341685979302841171 5218445012528968954261757)
                    ·
                      refine ⟨1956916879698363357848159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218445012528968954261757 1956916879698363357848159)
                      ·
                        rfl

theorem cell23_3811082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3811082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811082 prefixEnd_3811082 := by exact prefixLift 3811082
  have htrace : WordTrace (prefixWord ++ tailWord_3811082) baseStart_3811082 baseEnd_3811082 := by
    simpa [prefixWord, tailWord_3811082, baseEnd_3811082] using wordTrace_append hprefix tailTrace_3811082
  have hstable : (prefixWord ++ tailWord_3811082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811082).length < 2 ^ (prefixWord ++ tailWord_3811082).sum := by decide
  have hdescent : baseEnd_3811082 < baseStart_3811082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811116 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_3811116 : Nat := 118140960795 + 3811116 * 2 ^ 59
def prefixEnd_3811116 : Nat := 4983230072969 + 3 ^ 40 * 3811116 * 2
def baseEnd_3811116 : Nat := 1956934338040616224823003

theorem tailTrace_3811116 : CollatzResearch.WordTrace tailWord_3811116 prefixEnd_3811116 1956934338040616224823003 := by
  unfold tailWord_3811116
  simp only [CollatzResearch.WordTrace]
  refine ⟨69501410030492546819082601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92668546707323395758776801 69501410030492546819082601)
  ·
    refine ⟨52126057522869410114311951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69501410030492546819082601 52126057522869410114311951)
    ·
      refine ⟨78189086284304115171467927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52126057522869410114311951 78189086284304115171467927)
      ·
        refine ⟨117283629426456172757201891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78189086284304115171467927 117283629426456172757201891)
        ·
          refine ⟨175925444139684259135802837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117283629426456172757201891 175925444139684259135802837)
          ·
            refine ⟨4123252597023849823495379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175925444139684259135802837 4123252597023849823495379)
            ·
              refine ⟨6184878895535774735243069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123252597023849823495379 6184878895535774735243069)
              ·
                refine ⟨2319329585825915525716151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6184878895535774735243069 2319329585825915525716151)
                ·
                  refine ⟨3478994378738873288574227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319329585825915525716151 3478994378738873288574227)
                  ·
                    refine ⟨5218491568108309932861341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3478994378738873288574227 5218491568108309932861341)
                    ·
                      refine ⟨1956934338040616224823003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218491568108309932861341 1956934338040616224823003)
                      ·
                        rfl

theorem cell23_3811116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_3811116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811116 prefixEnd_3811116 := by exact prefixLift 3811116
  have htrace : WordTrace (prefixWord ++ tailWord_3811116) baseStart_3811116 baseEnd_3811116 := by
    simpa [prefixWord, tailWord_3811116, baseEnd_3811116] using wordTrace_append hprefix tailTrace_3811116
  have hstable : (prefixWord ++ tailWord_3811116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811116).length < 2 ^ (prefixWord ++ tailWord_3811116).sum := by decide
  have hdescent : baseEnd_3811116 < baseStart_3811116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811122 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3811122 : Nat := 118140960795 + 3811122 * 2 ^ 59
def prefixEnd_3811122 : Nat := 4983230072969 + 3 ^ 40 * 3811122 * 2
def baseEnd_3811122 : Nat := 1956937418924543201347975

theorem tailTrace_3811122 : CollatzResearch.WordTrace tailWord_3811122 prefixEnd_3811122 1956937418924543201347975 := by
  unfold tailWord_3811122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34750759724740839165720905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92668692599308904441922413 34750759724740839165720905)
  ·
    refine ⟨26063069793555629374290679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34750759724740839165720905 26063069793555629374290679)
    ·
      refine ⟨39094604690333444061436019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26063069793555629374290679 39094604690333444061436019)
      ·
        refine ⟨58641907035500166092154029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39094604690333444061436019 58641907035500166092154029)
        ·
          refine ⟨21990715138312562284557761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58641907035500166092154029 21990715138312562284557761)
          ·
            refine ⟨16493036353734421713418321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21990715138312562284557761 16493036353734421713418321)
            ·
              refine ⟨12369777265300816285063741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493036353734421713418321 12369777265300816285063741)
              ·
                refine ⟨4638666474487806106898903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12369777265300816285063741 4638666474487806106898903)
                ·
                  refine ⟨6957999711731709160348355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638666474487806106898903 6957999711731709160348355)
                  ·
                    refine ⟨10436999567597563740522533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957999711731709160348355 10436999567597563740522533)
                    ·
                      refine ⟨1956937418924543201347975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10436999567597563740522533 1956937418924543201347975)
                      ·
                        rfl

theorem cell23_3811122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3811122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811122 prefixEnd_3811122 := by exact prefixLift 3811122
  have htrace : WordTrace (prefixWord ++ tailWord_3811122) baseStart_3811122 baseEnd_3811122 := by
    simpa [prefixWord, tailWord_3811122, baseEnd_3811122] using wordTrace_append hprefix tailTrace_3811122
  have hstable : (prefixWord ++ tailWord_3811122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811122).length < 2 ^ (prefixWord ++ tailWord_3811122).sum := by decide
  have hdescent : baseEnd_3811122 < baseStart_3811122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811126 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_3811126 : Nat := 118140960795 + 3811126 * 2 ^ 59
def prefixEnd_3811126 : Nat := 4983230072969 + 3 ^ 40 * 3811126 * 2
def baseEnd_3811126 : Nat := 1956939472847161185697957

theorem tailTrace_3811126 : CollatzResearch.WordTrace tailWord_3811126 prefixEnd_3811126 1956939472847161185697957 := by
  unfold tailWord_3811126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687699049434304084126827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92668789860632576897352821 8687699049434304084126827)
  ·
    refine ⟨13031548574151456126190241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687699049434304084126827 13031548574151456126190241)
    ·
      refine ⟨9773661430613592094642681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13031548574151456126190241 9773661430613592094642681)
      ·
        refine ⟨7330246072960194070982011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9773661430613592094642681 7330246072960194070982011)
        ·
          refine ⟨10995369109440291106473017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330246072960194070982011 10995369109440291106473017)
          ·
            refine ⟨8246526832080218329854763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10995369109440291106473017 8246526832080218329854763)
            ·
              refine ⟨12369790248120327494782145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246526832080218329854763 12369790248120327494782145)
              ·
                refine ⟨9277342686090245621086609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12369790248120327494782145 9277342686090245621086609)
                ·
                  refine ⟨6958007014567684215814957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277342686090245621086609 6958007014567684215814957)
                  ·
                    refine ⟨2609252630462881580930609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6958007014567684215814957 2609252630462881580930609)
                    ·
                      refine ⟨1956939472847161185697957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609252630462881580930609 1956939472847161185697957)
                      ·
                        rfl

theorem cell23_3811126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_3811126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811126 prefixEnd_3811126 := by exact prefixLift 3811126
  have htrace : WordTrace (prefixWord ++ tailWord_3811126) baseStart_3811126 baseEnd_3811126 := by
    simpa [prefixWord, tailWord_3811126, baseEnd_3811126] using wordTrace_append hprefix tailTrace_3811126
  have hstable : (prefixWord ++ tailWord_3811126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811126).length < 2 ^ (prefixWord ++ tailWord_3811126).sum := by decide
  have hdescent : baseEnd_3811126 < baseStart_3811126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811128 : List Nat := [2, 1, 2, 1, 3, 3, 11]
def baseStart_3811128 : Nat := 118140960795 + 3811128 * 2 ^ 59
def prefixEnd_3811128 : Nat := 4983230072969 + 3 ^ 40 * 3811128 * 2
def baseEnd_3811128 : Nat := 24159759256894693553987

theorem tailTrace_3811128 : CollatzResearch.WordTrace tailWord_3811128 prefixEnd_3811128 24159759256894693553987 := by
  unfold tailWord_3811128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69501628868470809843801019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92668838491294413125068025 69501628868470809843801019)
  ·
    refine ⟨104252443302706214765701529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69501628868470809843801019 104252443302706214765701529)
    ·
      refine ⟨78189332477029661074276147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104252443302706214765701529 78189332477029661074276147)
      ·
        refine ⟨117283998715544491611414221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78189332477029661074276147 117283998715544491611414221)
        ·
          refine ⟨43981499518329184354280333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117283998715544491611414221 43981499518329184354280333)
          ·
            refine ⟨16493062319373444132855125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43981499518329184354280333 16493062319373444132855125)
            ·
              refine ⟨24159759256894693553987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16493062319373444132855125 24159759256894693553987)
              ·
                rfl

theorem cell23_3811128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 11].length) (baseStart_3811128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811128 prefixEnd_3811128 := by exact prefixLift 3811128
  have htrace : WordTrace (prefixWord ++ tailWord_3811128) baseStart_3811128 baseEnd_3811128 := by
    simpa [prefixWord, tailWord_3811128, baseEnd_3811128] using wordTrace_append hprefix tailTrace_3811128
  have hstable : (prefixWord ++ tailWord_3811128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811128).length < 2 ^ (prefixWord ++ tailWord_3811128).sum := by decide
  have hdescent : baseEnd_3811128 < baseStart_3811128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811133 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3811133 : Nat := 118140960795 + 3811133 * 2 ^ 59
def prefixEnd_3811133 : Nat := 4983230072969 + 3 ^ 40 * 3811133 * 2
def baseEnd_3811133 : Nat := 1956943067211742658310425

theorem tailTrace_3811133 : CollatzResearch.WordTrace tailWord_3811133 prefixEnd_3811133 1956943067211742658310425 := by
  unfold tailWord_3811133
  simp only [CollatzResearch.WordTrace]
  refine ⟨139003440101923505541534053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92668960067949003694356035 139003440101923505541534053)
  ·
    refine ⟨26063145019110657289037635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139003440101923505541534053 26063145019110657289037635)
    ·
      refine ⟨39094717528665985933556453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26063145019110657289037635 39094717528665985933556453)
      ·
        refine ⟨7330259536624872362541835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39094717528665985933556453 7330259536624872362541835)
        ·
          refine ⟨10995389304937308543812753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330259536624872362541835 10995389304937308543812753)
          ·
            refine ⟨8246541978702981407859565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10995389304937308543812753 8246541978702981407859565)
            ·
              refine ⟨3092453242013618027947337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8246541978702981407859565 3092453242013618027947337)
              ·
                refine ⟨2319339931510213520960503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092453242013618027947337 2319339931510213520960503)
                ·
                  refine ⟨3479009897265320281440755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319339931510213520960503 3479009897265320281440755)
                  ·
                    refine ⟨5218514845897980422161133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479009897265320281440755 5218514845897980422161133)
                    ·
                      refine ⟨1956943067211742658310425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218514845897980422161133 1956943067211742658310425)
                      ·
                        rfl

theorem cell23_3811133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3811133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811133 prefixEnd_3811133 := by exact prefixLift 3811133
  have htrace : WordTrace (prefixWord ++ tailWord_3811133) baseStart_3811133 baseEnd_3811133 := by
    simpa [prefixWord, tailWord_3811133, baseEnd_3811133] using wordTrace_append hprefix tailTrace_3811133
  have hstable : (prefixWord ++ tailWord_3811133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811133).length < 2 ^ (prefixWord ++ tailWord_3811133).sum := by decide
  have hdescent : baseEnd_3811133 < baseStart_3811133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811139 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 3, 2, 2]
def baseStart_3811139 : Nat := 118140960795 + 3811139 * 2 ^ 59
def prefixEnd_3811139 : Nat := 4983230072969 + 3 ^ 40 * 3811139 * 2
def baseEnd_3811139 : Nat := 1956946148095669634835397

theorem tailTrace_3811139 : CollatzResearch.WordTrace tailWord_3811139 prefixEnd_3811139 1956946148095669634835397 := by
  unfold tailWord_3811139
  simp only [CollatzResearch.WordTrace]
  refine ⟨139003658939901768566252471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92669105959934512377501647 139003658939901768566252471)
  ·
    refine ⟨208505488409852652849378707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139003658939901768566252471 208505488409852652849378707)
    ·
      refine ⟨312758232614778979274068061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208505488409852652849378707 312758232614778979274068061)
      ·
        refine ⟨117284337230542117227775523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312758232614778979274068061 117284337230542117227775523)
        ·
          refine ⟨175926505845813175841663285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117284337230542117227775523 175926505845813175841663285)
          ·
            refine ⟨16493109923044985235155933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175926505845813175841663285 16493109923044985235155933)
            ·
              refine ⟨6184916221141869463183475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16493109923044985235155933 6184916221141869463183475)
              ·
                refine ⟨9277374331712804194775213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184916221141869463183475 9277374331712804194775213)
                ·
                  refine ⟨3479015374392301573040705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9277374331712804194775213 3479015374392301573040705)
                  ·
                    refine ⟨2609261530794226179780529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479015374392301573040705 2609261530794226179780529)
                    ·
                      refine ⟨1956946148095669634835397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609261530794226179780529 1956946148095669634835397)
                      ·
                        rfl

theorem cell23_3811139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_3811139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811139 prefixEnd_3811139 := by exact prefixLift 3811139
  have htrace : WordTrace (prefixWord ++ tailWord_3811139) baseStart_3811139 baseEnd_3811139 := by
    simpa [prefixWord, tailWord_3811139, baseEnd_3811139] using wordTrace_append hprefix tailTrace_3811139
  have hstable : (prefixWord ++ tailWord_3811139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811139).length < 2 ^ (prefixWord ++ tailWord_3811139).sum := by decide
  have hdescent : baseEnd_3811139 < baseStart_3811139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811190 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3811190 : Nat := 118140960795 + 3811190 * 2 ^ 59
def prefixEnd_3811190 : Nat := 4983230072969 + 3 ^ 40 * 3811190 * 2
def baseEnd_3811190 : Nat := 1956972335609048935297663

theorem tailTrace_3811190 : CollatzResearch.WordTrace tailWord_3811190 prefixEnd_3811190 1956972335609048935297663 := by
  unfold tailWord_3811190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687844941419812767272439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92670346041811336184239349 8687844941419812767272439)
  ·
    refine ⟨13031767412129719150908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687844941419812767272439 13031767412129719150908659)
    ·
      refine ⟨19547651118194578726362989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13031767412129719150908659 19547651118194578726362989)
      ·
        refine ⟨7330369169322967022386121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19547651118194578726362989 7330369169322967022386121)
        ·
          refine ⟨5497776876992225266789591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7330369169322967022386121 5497776876992225266789591)
          ·
            refine ⟨8246665315488337900184387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497776876992225266789591 8246665315488337900184387)
            ·
              refine ⟨12369997973232506850276581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246665315488337900184387 12369997973232506850276581)
              ·
                refine ⟨2319374619981095034426859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12369997973232506850276581 2319374619981095034426859)
                ·
                  refine ⟨3479061929971642551640289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319374619981095034426859 3479061929971642551640289)
                  ·
                    refine ⟨2609296447478731913730217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479061929971642551640289 2609296447478731913730217)
                    ·
                      refine ⟨1956972335609048935297663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609296447478731913730217 1956972335609048935297663)
                      ·
                        rfl

theorem cell23_3811190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3811190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811190 prefixEnd_3811190 := by exact prefixLift 3811190
  have htrace : WordTrace (prefixWord ++ tailWord_3811190) baseStart_3811190 baseEnd_3811190 := by
    simpa [prefixWord, tailWord_3811190, baseEnd_3811190] using wordTrace_append hprefix tailTrace_3811190
  have hstable : (prefixWord ++ tailWord_3811190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811190).length < 2 ^ (prefixWord ++ tailWord_3811190).sum := by decide
  have hdescent : baseEnd_3811190 < baseStart_3811190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811205 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3811205 : Nat := 118140960795 + 3811205 * 2 ^ 59
def prefixEnd_3811205 : Nat := 4983230072969 + 3 ^ 40 * 3811205 * 2
def baseEnd_3811205 : Nat := 652326679272955458870031

theorem tailTrace_3811205 : CollatzResearch.WordTrace tailWord_3811205 prefixEnd_3811205 652326679272955458870031 := by
  unfold tailWord_3811205
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006066157662661838155069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92670710771775107892103379 139006066157662661838155069)
  ·
    refine ⟨52127274809123498189308151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139006066157662661838155069 52127274809123498189308151)
    ·
      refine ⟨78190912213685247283962227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52127274809123498189308151 78190912213685247283962227)
      ·
        refine ⟨117286368320527870925943341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78190912213685247283962227 117286368320527870925943341)
        ·
          refine ⟨43982388120197951597228753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117286368320527870925943341 43982388120197951597228753)
          ·
            refine ⟨32986791090148463697921565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43982388120197951597228753 32986791090148463697921565)
            ·
              refine ⟨12370046658805673886720587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32986791090148463697921565 12370046658805673886720587)
              ·
                refine ⟨18555069988208510830080881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12370046658805673886720587 18555069988208510830080881)
                ·
                  refine ⟨13916302491156383122560661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18555069988208510830080881 13916302491156383122560661)
                  ·
                    refine ⟨652326679272955458870031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13916302491156383122560661 652326679272955458870031)
                    ·
                      rfl

theorem cell23_3811205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3811205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811205 prefixEnd_3811205 := by exact prefixLift 3811205
  have htrace : WordTrace (prefixWord ++ tailWord_3811205) baseStart_3811205 baseEnd_3811205 := by
    simpa [prefixWord, tailWord_3811205, baseEnd_3811205] using wordTrace_append hprefix tailTrace_3811205
  have hstable : (prefixWord ++ tailWord_3811205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811205).length < 2 ^ (prefixWord ++ tailWord_3811205).sum := by decide
  have hdescent : baseEnd_3811205 < baseStart_3811205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811229 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3811229 : Nat := 118140960795 + 3811229 * 2 ^ 59
def prefixEnd_3811229 : Nat := 4983230072969 + 3 ^ 40 * 3811229 * 2
def baseEnd_3811229 : Nat := 1956992361354574282709983

theorem tailTrace_3811229 : CollatzResearch.WordTrace tailWord_3811229 prefixEnd_3811229 1956992361354574282709983 := by
  unfold tailWord_3811229
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006941509575713937028741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92671294339717142624685827 139006941509575713937028741)
  ·
    refine ⟨26063801533045446363192889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139006941509575713937028741 26063801533045446363192889)
    ·
      refine ⟨19547851149784084772394667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26063801533045446363192889 19547851149784084772394667)
      ·
        refine ⟨29321776724676127158592001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19547851149784084772394667 29321776724676127158592001)
        ·
          refine ⟨21991332543507095368944001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29321776724676127158592001 21991332543507095368944001)
          ·
            refine ⟨16493499407630321526708001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21991332543507095368944001 16493499407630321526708001)
            ·
              refine ⟨12370124555722741145031001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16493499407630321526708001 12370124555722741145031001)
              ·
                refine ⟨9277593416792055858773251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370124555722741145031001 9277593416792055858773251)
                ·
                  refine ⟨13916390125188083788159877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9277593416792055858773251 13916390125188083788159877)
                  ·
                    refine ⟨2609323148472765710279977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13916390125188083788159877 2609323148472765710279977)
                    ·
                      refine ⟨1956992361354574282709983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609323148472765710279977 1956992361354574282709983)
                      ·
                        rfl

theorem cell23_3811229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3811229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811229 prefixEnd_3811229 := by exact prefixLift 3811229
  have htrace : WordTrace (prefixWord ++ tailWord_3811229) baseStart_3811229 baseEnd_3811229 := by
    simpa [prefixWord, tailWord_3811229, baseEnd_3811229] using wordTrace_append hprefix tailTrace_3811229
  have hstable : (prefixWord ++ tailWord_3811229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811229).length < 2 ^ (prefixWord ++ tailWord_3811229).sum := by decide
  have hdescent : baseEnd_3811229 < baseStart_3811229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811240 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3811240 : Nat := 118140960795 + 3811240 * 2 ^ 59
def prefixEnd_3811240 : Nat := 4983230072969 + 3 ^ 40 * 3811240 * 2
def baseEnd_3811240 : Nat := 1956998009641773739672433

theorem tailTrace_3811240 : CollatzResearch.WordTrace tailWord_3811240 prefixEnd_3811240 1956998009641773739672433 := by
  unfold tailWord_3811240
  simp only [CollatzResearch.WordTrace]
  refine ⟨69503671356267931407839587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92671561808357241877119449 69503671356267931407839587)
  ·
    refine ⟨104255507034401897111759381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69503671356267931407839587 104255507034401897111759381)
    ·
      refine ⟨4886976892237588927113721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104255507034401897111759381 4886976892237588927113721)
      ·
        refine ⟨3665232669178191695335291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886976892237588927113721 3665232669178191695335291)
        ·
          refine ⟨5497849003767287543002937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665232669178191695335291 5497849003767287543002937)
          ·
            refine ⟨4123386752825465657252203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5497849003767287543002937 4123386752825465657252203)
            ·
              refine ⟨6185080129238198485878305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123386752825465657252203 6185080129238198485878305)
              ·
                refine ⟨4638810096928648864408729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6185080129238198485878305 4638810096928648864408729)
                ·
                  refine ⟨3479107572696486648306547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638810096928648864408729 3479107572696486648306547)
                  ·
                    refine ⟨5218661359044729972459821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479107572696486648306547 5218661359044729972459821)
                    ·
                      refine ⟨1956998009641773739672433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218661359044729972459821 1956998009641773739672433)
                      ·
                        rfl

theorem cell23_3811240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3811240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811240 prefixEnd_3811240 := by exact prefixLift 3811240
  have htrace : WordTrace (prefixWord ++ tailWord_3811240) baseStart_3811240 baseEnd_3811240 := by
    simpa [prefixWord, tailWord_3811240, baseEnd_3811240] using wordTrace_append hprefix tailTrace_3811240
  have hstable : (prefixWord ++ tailWord_3811240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811240).length < 2 ^ (prefixWord ++ tailWord_3811240).sum := by decide
  have hdescent : baseEnd_3811240 < baseStart_3811240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811315 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_3811315 : Nat := 118140960795 + 3811315 * 2 ^ 59
def prefixEnd_3811315 : Nat := 4983230072969 + 3 ^ 40 * 3811315 * 2
def baseEnd_3811315 : Nat := 1957036520690860946234587

theorem tailTrace_3811315 : CollatzResearch.WordTrace tailWord_3811315 prefixEnd_3811315 1957036520690860946234587 := by
  unfold tailWord_3811315
  simp only [CollatzResearch.WordTrace]
  refine ⟨139010078187264150624659399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92673385458176100416439599 139010078187264150624659399)
  ·
    refine ⟨208515117280896225936989099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139010078187264150624659399 208515117280896225936989099)
    ·
      refine ⟨312772675921344338905483649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208515117280896225936989099 312772675921344338905483649)
      ·
        refine ⟨234579506941008254179112737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312772675921344338905483649 234579506941008254179112737)
        ·
          refine ⟨175934630205756190634334553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234579506941008254179112737 175934630205756190634334553)
          ·
            refine ⟨131950972654317142975750915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175934630205756190634334553 131950972654317142975750915)
            ·
              refine ⟨197926458981475714463626373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131950972654317142975750915 197926458981475714463626373)
              ·
                refine ⟨37111211059026696461929945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197926458981475714463626373 37111211059026696461929945)
                ·
                  refine ⟨27833408294270022346447459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37111211059026696461929945 27833408294270022346447459)
                  ·
                    refine ⟨41750112441405033519671189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27833408294270022346447459 41750112441405033519671189)
                    ·
                      refine ⟨1957036520690860946234587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41750112441405033519671189 1957036520690860946234587)
                      ·
                        rfl

theorem cell23_3811315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_3811315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811315 prefixEnd_3811315 := by exact prefixLift 3811315
  have htrace : WordTrace (prefixWord ++ tailWord_3811315) baseStart_3811315 baseEnd_3811315 := by
    simpa [prefixWord, tailWord_3811315, baseEnd_3811315] using wordTrace_append hprefix tailTrace_3811315
  have hstable : (prefixWord ++ tailWord_3811315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811315).length < 2 ^ (prefixWord ++ tailWord_3811315).sum := by decide
  have hdescent : baseEnd_3811315 < baseStart_3811315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811339 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3]
def baseStart_3811339 : Nat := 118140960795 + 3811339 * 2 ^ 59
def prefixEnd_3811339 : Nat := 4983230072969 + 3 ^ 40 * 3811339 * 2
def baseEnd_3811339 : Nat := 1957048844226568852334477

theorem tailTrace_3811339 : CollatzResearch.WordTrace tailWord_3811339 prefixEnd_3811339 1957048844226568852334477 := by
  unfold tailWord_3811339
  simp only [CollatzResearch.WordTrace]
  refine ⟨139010953539177202723533071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92673969026118135149022047 139010953539177202723533071)
  ·
    refine ⟨208516430308765804085299607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139010953539177202723533071 208516430308765804085299607)
    ·
      refine ⟨312774645463148706127949411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208516430308765804085299607 312774645463148706127949411)
      ·
        refine ⟨469161968194723059191924117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312774645463148706127949411 469161968194723059191924117)
        ·
          refine ⟨21991967259127643399621443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 469161968194723059191924117 21991967259127643399621443)
          ·
            refine ⟨32987950888691465099432165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21991967259127643399621443 32987950888691465099432165)
            ·
              refine ⟨6185240791629649706143531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32987950888691465099432165 6185240791629649706143531)
              ·
                refine ⟨9277861187444474559215297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185240791629649706143531 9277861187444474559215297)
                ·
                  refine ⟨6958395890583355919411473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277861187444474559215297 6958395890583355919411473)
                  ·
                    refine ⟨5218796917937516939558605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6958395890583355919411473 5218796917937516939558605)
                    ·
                      refine ⟨1957048844226568852334477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218796917937516939558605 1957048844226568852334477)
                      ·
                        rfl

theorem cell23_3811339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 3].length) (baseStart_3811339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811339 prefixEnd_3811339 := by exact prefixLift 3811339
  have htrace : WordTrace (prefixWord ++ tailWord_3811339) baseStart_3811339 baseEnd_3811339 := by
    simpa [prefixWord, tailWord_3811339, baseEnd_3811339] using wordTrace_append hprefix tailTrace_3811339
  have hstable : (prefixWord ++ tailWord_3811339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811339).length < 2 ^ (prefixWord ++ tailWord_3811339).sum := by decide
  have hdescent : baseEnd_3811339 < baseStart_3811339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811345 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_3811345 : Nat := 118140960795 + 3811345 * 2 ^ 59
def prefixEnd_3811345 : Nat := 4983230072969 + 3 ^ 40 * 3811345 * 2
def baseEnd_3811345 : Nat := 1957051925110495828859449

theorem tailTrace_3811345 : CollatzResearch.WordTrace tailWord_3811345 prefixEnd_3811345 1957051925110495828859449 := by
  unfold tailWord_3811345
  simp only [CollatzResearch.WordTrace]
  refine ⟨139011172377155465748251489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92674114918103643832167659 139011172377155465748251489)
  ·
    refine ⟨104258379282866599311188617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139011172377155465748251489 104258379282866599311188617)
    ·
      refine ⟨78193784462149949483391463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104258379282866599311188617 78193784462149949483391463)
      ·
        refine ⟨117290676693224924225087195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78193784462149949483391463 117290676693224924225087195)
        ·
          refine ⟨175936015039837386337630793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117290676693224924225087195 175936015039837386337630793)
          ·
            refine ⟨131952011279878039753223095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175936015039837386337630793 131952011279878039753223095)
            ·
              refine ⟨197928016919817059629834643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131952011279878039753223095 197928016919817059629834643)
              ·
                refine ⟨296892025379725589444751965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197928016919817059629834643 296892025379725589444751965)
                ·
                  refine ⟨111334509517397096041781987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296892025379725589444751965 111334509517397096041781987)
                  ·
                    refine ⟨167001764276095644062672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111334509517397096041781987 167001764276095644062672981)
                    ·
                      refine ⟨1957051925110495828859449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 167001764276095644062672981 1957051925110495828859449)
                      ·
                        rfl

theorem cell23_3811345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_3811345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811345 prefixEnd_3811345 := by exact prefixLift 3811345
  have htrace : WordTrace (prefixWord ++ tailWord_3811345) baseStart_3811345 baseEnd_3811345 := by
    simpa [prefixWord, tailWord_3811345, baseEnd_3811345] using wordTrace_append hprefix tailTrace_3811345
  have hstable : (prefixWord ++ tailWord_3811345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811345).length < 2 ^ (prefixWord ++ tailWord_3811345).sum := by decide
  have hdescent : baseEnd_3811345 < baseStart_3811345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811362 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3811362 : Nat := 118140960795 + 3811362 * 2 ^ 59
def prefixEnd_3811362 : Nat := 4983230072969 + 3 ^ 40 * 3811362 * 2
def baseEnd_3811362 : Nat := 1957060654281622262346871

theorem tailTrace_3811362 : CollatzResearch.WordTrace tailWord_3811362 prefixEnd_3811362 1957060654281622262346871 := by
  unfold tailWord_3811362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34752948104523469412905085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92674528278729251767746893 34752948104523469412905085)
  ·
    refine ⟨13032355539196301029839407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34752948104523469412905085 13032355539196301029839407)
    ·
      refine ⟨19548533308794451544759111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032355539196301029839407 19548533308794451544759111)
      ·
        refine ⟨29322799963191677317138667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19548533308794451544759111 29322799963191677317138667)
        ·
          refine ⟨43984199944787515975708001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29322799963191677317138667 43984199944787515975708001)
          ·
            refine ⟨32988149958590636981781001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43984199944787515975708001 32988149958590636981781001)
            ·
              refine ⟨24741112468942977736335751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32988149958590636981781001 24741112468942977736335751)
              ·
                refine ⟨37111668703414466604503627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24741112468942977736335751 37111668703414466604503627)
                ·
                  refine ⟨55667503055121699906755441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37111668703414466604503627 55667503055121699906755441)
                  ·
                    refine ⟨41750627291341274930066581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55667503055121699906755441 41750627291341274930066581)
                    ·
                      refine ⟨1957060654281622262346871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41750627291341274930066581 1957060654281622262346871)
                      ·
                        rfl

theorem cell23_3811362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3811362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811362 prefixEnd_3811362 := by exact prefixLift 3811362
  have htrace : WordTrace (prefixWord ++ tailWord_3811362) baseStart_3811362 baseEnd_3811362 := by
    simpa [prefixWord, tailWord_3811362, baseEnd_3811362] using wordTrace_append hprefix tailTrace_3811362
  have hstable : (prefixWord ++ tailWord_3811362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811362).length < 2 ^ (prefixWord ++ tailWord_3811362).sum := by decide
  have hdescent : baseEnd_3811362 < baseStart_3811362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811379 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 4, 3, 2]
def baseStart_3811379 : Nat := 118140960795 + 3811379 * 2 ^ 59
def prefixEnd_3811379 : Nat := 4983230072969 + 3 ^ 40 * 3811379 * 2
def baseEnd_3811379 : Nat := 1957069383452748695834293

theorem tailTrace_3811379 : CollatzResearch.WordTrace tailWord_3811379 prefixEnd_3811379 1957069383452748695834293 := by
  unfold tailWord_3811379
  simp only [CollatzResearch.WordTrace]
  refine ⟨139012412459032289554989191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92674941639354859703326127 139012412459032289554989191)
  ·
    refine ⟨208518618688548434332483787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139012412459032289554989191 208518618688548434332483787)
    ·
      refine ⟨312777928032822651498725681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208518618688548434332483787 312777928032822651498725681)
      ·
        refine ⟨234583446024616988624044261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312777928032822651498725681 234583446024616988624044261)
        ·
          refine ⟨43984396129615685367008299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234583446024616988624044261 43984396129615685367008299)
          ·
            refine ⟨65976594194423528050512449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43984396129615685367008299 65976594194423528050512449)
            ·
              refine ⟨49482445645817646037884337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65976594194423528050512449 49482445645817646037884337)
              ·
                refine ⟨37111834234363234528413253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49482445645817646037884337 37111834234363234528413253)
                ·
                  refine ⟨6958468918943106474077485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37111834234363234528413253 6958468918943106474077485)
                  ·
                    refine ⟨2609425844603664927779057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6958468918943106474077485 2609425844603664927779057)
                    ·
                      refine ⟨1957069383452748695834293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609425844603664927779057 1957069383452748695834293)
                      ·
                        rfl

theorem cell23_3811379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 3, 2].length) (baseStart_3811379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811379 prefixEnd_3811379 := by exact prefixLift 3811379
  have htrace : WordTrace (prefixWord ++ tailWord_3811379) baseStart_3811379 baseEnd_3811379 := by
    simpa [prefixWord, tailWord_3811379, baseEnd_3811379] using wordTrace_append hprefix tailTrace_3811379
  have hstable : (prefixWord ++ tailWord_3811379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811379).length < 2 ^ (prefixWord ++ tailWord_3811379).sum := by decide
  have hdescent : baseEnd_3811379 < baseStart_3811379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811389 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3811389 : Nat := 118140960795 + 3811389 * 2 ^ 59
def prefixEnd_3811389 : Nat := 4983230072969 + 3 ^ 40 * 3811389 * 2
def baseEnd_3811389 : Nat := 652358172753097885569749

theorem tailTrace_3811389 : CollatzResearch.WordTrace tailWord_3811389 prefixEnd_3811389 652358172753097885569749 := by
  unfold tailWord_3811389
  simp only [CollatzResearch.WordTrace]
  refine ⟨139012777188996061262853221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92675184792664040841902147 139012777188996061262853221)
  ·
    refine ⟨26064895722936761486784979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139012777188996061262853221 26064895722936761486784979)
    ·
      refine ⟨39097343584405142230177469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26064895722936761486784979 39097343584405142230177469)
      ·
        refine ⟨14661503844151928336316551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39097343584405142230177469 14661503844151928336316551)
        ·
          refine ⟨21992255766227892504474827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14661503844151928336316551 21992255766227892504474827)
          ·
            refine ⟨32988383649341838756712241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21992255766227892504474827 32988383649341838756712241)
            ·
              refine ⟨24741287737006379067534181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32988383649341838756712241 24741287737006379067534181)
              ·
                refine ⟨4638991450688696075162659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24741287737006379067534181 4638991450688696075162659)
                ·
                  refine ⟨6958487176033044112743989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638991450688696075162659 6958487176033044112743989)
                  ·
                    refine ⟨652358172753097885569749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6958487176033044112743989 652358172753097885569749)
                    ·
                      rfl

theorem cell23_3811389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3811389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811389 prefixEnd_3811389 := by exact prefixLift 3811389
  have htrace : WordTrace (prefixWord ++ tailWord_3811389) baseStart_3811389 baseEnd_3811389 := by
    simpa [prefixWord, tailWord_3811389, baseEnd_3811389] using wordTrace_append hprefix tailTrace_3811389
  have hstable : (prefixWord ++ tailWord_3811389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811389).length < 2 ^ (prefixWord ++ tailWord_3811389).sum := by decide
  have hdescent : baseEnd_3811389 < baseStart_3811389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811390 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3811390 : Nat := 118140960795 + 3811390 * 2 ^ 59
def prefixEnd_3811390 : Nat := 4983230072969 + 3 ^ 40 * 3811390 * 2
def baseEnd_3811390 : Nat := 1957075031739948152796743

theorem tailTrace_3811390 : CollatzResearch.WordTrace tailWord_3811390 prefixEnd_3811390 1957075031739948152796743 := by
  unfold tailWord_3811390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376601707749054804204953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92675209107994958955759749 17376601707749054804204953)
  ·
    refine ⟨13032451280811791103153715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17376601707749054804204953 13032451280811791103153715)
    ·
      refine ⟨19548676921217686654730573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032451280811791103153715 19548676921217686654730573)
      ·
        refine ⟨7330753845456632495523965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19548676921217686654730573 7330753845456632495523965)
        ·
          refine ⟨2749032692046237185821487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7330753845456632495523965 2749032692046237185821487)
          ·
            refine ⟨4123549038069355778732231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749032692046237185821487 4123549038069355778732231)
            ·
              refine ⟨6185323557104033668098347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123549038069355778732231 6185323557104033668098347)
              ·
                refine ⟨9277985335656050502147521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185323557104033668098347 9277985335656050502147521)
                ·
                  refine ⟨6958489001742037876610641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277985335656050502147521 6958489001742037876610641)
                  ·
                    refine ⟨5218866751306528407457981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6958489001742037876610641 5218866751306528407457981)
                    ·
                      refine ⟨1957075031739948152796743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5218866751306528407457981 1957075031739948152796743)
                      ·
                        rfl

theorem cell23_3811390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3811390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811390 prefixEnd_3811390 := by exact prefixLift 3811390
  have htrace : WordTrace (prefixWord ++ tailWord_3811390) baseStart_3811390 baseEnd_3811390 := by
    simpa [prefixWord, tailWord_3811390, baseEnd_3811390] using wordTrace_append hprefix tailTrace_3811390
  have hstable : (prefixWord ++ tailWord_3811390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811390).length < 2 ^ (prefixWord ++ tailWord_3811390).sum := by decide
  have hdescent : baseEnd_3811390 < baseStart_3811390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811406 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_3811406 : Nat := 118140960795 + 3811406 * 2 ^ 59
def prefixEnd_3811406 : Nat := 4983230072969 + 3 ^ 40 * 3811406 * 2
def baseEnd_3811406 : Nat := 652361082476806696732223

theorem tailTrace_3811406 : CollatzResearch.WordTrace tailWord_3811406 prefixEnd_3811406 652361082476806696732223 := by
  unfold tailWord_3811406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376674653741809145777759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92675598153289648777481381 17376674653741809145777759)
  ·
    refine ⟨26065011980612713718666639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17376674653741809145777759 26065011980612713718666639)
    ·
      refine ⟨39097517970919070577999959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26065011980612713718666639 39097517970919070577999959)
      ·
        refine ⟨58646276956378605866999939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39097517970919070577999959 58646276956378605866999939)
        ·
          refine ⟨87969415434567908800499909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58646276956378605866999939 87969415434567908800499909)
          ·
            refine ⟨16494265393981482900093733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87969415434567908800499909 16494265393981482900093733)
            ·
              refine ⟨3092674761371528043767575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16494265393981482900093733 3092674761371528043767575)
              ·
                refine ⟨4639012142057292065651363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092674761371528043767575 4639012142057292065651363)
                ·
                  refine ⟨6958518213085938098477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639012142057292065651363 6958518213085938098477045)
                  ·
                    refine ⟨652361082476806696732223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6958518213085938098477045 652361082476806696732223)
                    ·
                      rfl

theorem cell23_3811406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_3811406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811406 prefixEnd_3811406 := by exact prefixLift 3811406
  have htrace : WordTrace (prefixWord ++ tailWord_3811406) baseStart_3811406 baseEnd_3811406 := by
    simpa [prefixWord, tailWord_3811406, baseEnd_3811406] using wordTrace_append hprefix tailTrace_3811406
  have hstable : (prefixWord ++ tailWord_3811406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811406).length < 2 ^ (prefixWord ++ tailWord_3811406).sum := by decide
  have hdescent : baseEnd_3811406 < baseStart_3811406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811429 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3811429 : Nat := 118140960795 + 3811429 * 2 ^ 59
def prefixEnd_3811429 : Nat := 4983230072969 + 3 ^ 40 * 3811429 * 2
def baseEnd_3811429 : Nat := 1957095057485473500209063

theorem tailTrace_3811429 : CollatzResearch.WordTrace tailWord_3811429 prefixEnd_3811429 1957095057485473500209063 := by
  unfold tailWord_3811429
  simp only [CollatzResearch.WordTrace]
  refine ⟨139014236108851148094309341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92676157405900765396206227 139014236108851148094309341)
  ·
    refine ⟨52130338540819180535366003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139014236108851148094309341 52130338540819180535366003)
    ·
      refine ⟨78195507811228770803049005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52130338540819180535366003 78195507811228770803049005)
      ·
        refine ⟨29323315429210789051143377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78195507811228770803049005 29323315429210789051143377)
        ·
          refine ⟨21992486571908091788357533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29323315429210789051143377 21992486571908091788357533)
          ·
            refine ⟨8247182464465534420634075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21992486571908091788357533 8247182464465534420634075)
            ·
              refine ⟨12370773696698301630951113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247182464465534420634075 12370773696698301630951113)
              ·
                refine ⟨9278080272523726223213335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370773696698301630951113 9278080272523726223213335)
                ·
                  refine ⟨13917120408785589334820003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278080272523726223213335 13917120408785589334820003)
                  ·
                    refine ⟨20875680613178384002230005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13917120408785589334820003 20875680613178384002230005)
                    ·
                      refine ⟨1957095057485473500209063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20875680613178384002230005 1957095057485473500209063)
                      ·
                        rfl

theorem cell23_3811429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3811429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811429 prefixEnd_3811429 := by exact prefixLift 3811429
  have htrace : WordTrace (prefixWord ++ tailWord_3811429) baseStart_3811429 baseEnd_3811429 := by
    simpa [prefixWord, tailWord_3811429, baseEnd_3811429] using wordTrace_append hprefix tailTrace_3811429
  have hstable : (prefixWord ++ tailWord_3811429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811429).length < 2 ^ (prefixWord ++ tailWord_3811429).sum := by decide
  have hdescent : baseEnd_3811429 < baseStart_3811429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811439 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_3811439 : Nat := 118140960795 + 3811439 * 2 ^ 59
def prefixEnd_3811439 : Nat := 4983230072969 + 3 ^ 40 * 3811439 * 2
def baseEnd_3811439 : Nat := 1957100192292018461084017

theorem tailTrace_3811439 : CollatzResearch.WordTrace tailWord_3811439 prefixEnd_3811439 1957100192292018461084017 := by
  unfold tailWord_3811439
  simp only [CollatzResearch.WordTrace]
  refine ⟨139014600838814919802173371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92676400559209946534782247 139014600838814919802173371)
  ·
    refine ⟨208521901258222379703260057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139014600838814919802173371 208521901258222379703260057)
    ·
      refine ⟨156391425943666784777445043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208521901258222379703260057 156391425943666784777445043)
      ·
        refine ⟨234587138915500177166167565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156391425943666784777445043 234587138915500177166167565)
        ·
          refine ⟨87970177093312566437312837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234587138915500177166167565 87970177093312566437312837)
          ·
            refine ⟨16494408204996106206996157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87970177093312566437312837 16494408204996106206996157)
            ·
              refine ⟨6185403076873539827623559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16494408204996106206996157 6185403076873539827623559)
              ·
                refine ⟨9278104615310309741435339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185403076873539827623559 9278104615310309741435339)
                ·
                  refine ⟨13917156922965464612153009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9278104615310309741435339 13917156922965464612153009)
                  ·
                    refine ⟨10437867692224098459114757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13917156922965464612153009 10437867692224098459114757)
                    ·
                      refine ⟨1957100192292018461084017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10437867692224098459114757 1957100192292018461084017)
                      ·
                        rfl

theorem cell23_3811439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_3811439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811439 prefixEnd_3811439 := by exact prefixLift 3811439
  have htrace : WordTrace (prefixWord ++ tailWord_3811439) baseStart_3811439 baseEnd_3811439 := by
    simpa [prefixWord, tailWord_3811439, baseEnd_3811439] using wordTrace_append hprefix tailTrace_3811439
  have hstable : (prefixWord ++ tailWord_3811439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811439).length < 2 ^ (prefixWord ++ tailWord_3811439).sum := by decide
  have hdescent : baseEnd_3811439 < baseStart_3811439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811449 : List Nat := [1, 2, 1, 3, 4, 1, 4, 7]
def baseStart_3811449 : Nat := 118140960795 + 3811449 * 2 ^ 59
def prefixEnd_3811449 : Nat := 4983230072969 + 3 ^ 40 * 3811449 * 2
def baseEnd_3811449 : Nat := 72485382485131978591073

theorem tailTrace_3811449 : CollatzResearch.WordTrace tailWord_3811449 prefixEnd_3811449 72485382485131978591073 := by
  unfold tailWord_3811449
  simp only [CollatzResearch.WordTrace]
  refine ⟨139014965568778691510037401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92676643712519127673358267 139014965568778691510037401)
  ·
    refine ⟨104261224176584018632528051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139014965568778691510037401 104261224176584018632528051)
    ·
      refine ⟨156391836264876027948792077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104261224176584018632528051 156391836264876027948792077)
      ·
        refine ⟨58646938599328510480797029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156391836264876027948792077 58646938599328510480797029)
        ·
          refine ⟨10996300987374095715149443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58646938599328510480797029 10996300987374095715149443)
          ·
            refine ⟨16494451481061143572724165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996300987374095715149443 16494451481061143572724165)
            ·
              refine ⟨3092709652698964419885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16494451481061143572724165 3092709652698964419885781)
              ·
                refine ⟨72485382485131978591073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3092709652698964419885781 72485382485131978591073)
                ·
                  rfl

theorem cell23_3811449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 7].length) (baseStart_3811449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811449 prefixEnd_3811449 := by exact prefixLift 3811449
  have htrace : WordTrace (prefixWord ++ tailWord_3811449) baseStart_3811449 baseEnd_3811449 := by
    simpa [prefixWord, tailWord_3811449, baseEnd_3811449] using wordTrace_append hprefix tailTrace_3811449
  have hstable : (prefixWord ++ tailWord_3811449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811449).length < 2 ^ (prefixWord ++ tailWord_3811449).sum := by decide
  have hdescent : baseEnd_3811449 < baseStart_3811449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811472 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_3811472 : Nat := 118140960795 + 3811472 * 2 ^ 59
def prefixEnd_3811472 : Nat := 4983230072969 + 3 ^ 40 * 3811472 * 2
def baseEnd_3811472 : Nat := 1957117137153616831971365

theorem tailTrace_3811472 : CollatzResearch.WordTrace tailWord_3811472 prefixEnd_3811472 1957117137153616831971365 := by
  unfold tailWord_3811472
  simp only [CollatzResearch.WordTrace]
  refine ⟨69507902223847683219062335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92677202965130244292083113 69507902223847683219062335)
  ·
    refine ⟨104261853335771524828593503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69507902223847683219062335 104261853335771524828593503)
    ·
      refine ⟨156392780003657287242890255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104261853335771524828593503 156392780003657287242890255)
      ·
        refine ⟨234589170005485930864335383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156392780003657287242890255 234589170005485930864335383)
        ·
          refine ⟨351883755008228896296503075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234589170005485930864335383 351883755008228896296503075)
          ·
            refine ⟨527825632512343344444754613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351883755008228896296503075 527825632512343344444754613)
            ·
              refine ⟨49483653048032188541695745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 527825632512343344444754613 49483653048032188541695745)
              ·
                refine ⟨37112739786024141406271809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49483653048032188541695745 37112739786024141406271809)
                ·
                  refine ⟨27834554839518106054703857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37112739786024141406271809 27834554839518106054703857)
                  ·
                    refine ⟨20875916129638579541027893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27834554839518106054703857 20875916129638579541027893)
                    ·
                      refine ⟨1957117137153616831971365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20875916129638579541027893 1957117137153616831971365)
                      ·
                        rfl

theorem cell23_3811472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_3811472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811472 prefixEnd_3811472 := by exact prefixLift 3811472
  have htrace : WordTrace (prefixWord ++ tailWord_3811472) baseStart_3811472 baseEnd_3811472 := by
    simpa [prefixWord, tailWord_3811472, baseEnd_3811472] using wordTrace_append hprefix tailTrace_3811472
  have hstable : (prefixWord ++ tailWord_3811472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811472).length < 2 ^ (prefixWord ++ tailWord_3811472).sum := by decide
  have hdescent : baseEnd_3811472 < baseStart_3811472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811520 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2]
def baseStart_3811520 : Nat := 118140960795 + 3811520 * 2 ^ 59
def prefixEnd_3811520 : Nat := 4983230072969 + 3 ^ 40 * 3811520 * 2
def baseEnd_3811520 : Nat := 1957141784225032644171145

theorem tailTrace_3811520 : CollatzResearch.WordTrace tailWord_3811520 prefixEnd_3811520 1957141784225032644171145 := by
  unfold tailWord_3811520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69508777575760735317936007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92678370101014313757248009 69508777575760735317936007)
  ·
    refine ⟨104263166363641102976904011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69508777575760735317936007 104263166363641102976904011)
    ·
      refine ⟨156394749545461654465356017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104263166363641102976904011 156394749545461654465356017)
      ·
        refine ⟨117296062159096240849017013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156394749545461654465356017 117296062159096240849017013)
        ·
          refine ⟨10996505827415272579595345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117296062159096240849017013 10996505827415272579595345)
          ·
            refine ⟨8247379370561454434696509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996505827415272579595345 8247379370561454434696509)
            ·
              refine ⟨3092767263960545413011191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8247379370561454434696509 3092767263960545413011191)
              ·
                refine ⟨4639150895940818119516787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092767263960545413011191 4639150895940818119516787)
                ·
                  refine ⟨6958726343911227179275181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639150895940818119516787 6958726343911227179275181)
                  ·
                    refine ⟨2609522378966710192228193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6958726343911227179275181 2609522378966710192228193)
                    ·
                      refine ⟨1957141784225032644171145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609522378966710192228193 1957141784225032644171145)
                      ·
                        rfl

theorem cell23_3811520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_3811520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811520 prefixEnd_3811520 := by exact prefixLift 3811520
  have htrace : WordTrace (prefixWord ++ tailWord_3811520) baseStart_3811520 baseEnd_3811520 := by
    simpa [prefixWord, tailWord_3811520, baseEnd_3811520] using wordTrace_append hprefix tailTrace_3811520
  have hstable : (prefixWord ++ tailWord_3811520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811520).length < 2 ^ (prefixWord ++ tailWord_3811520).sum := by decide
  have hdescent : baseEnd_3811520 < baseStart_3811520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811619 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3811619 : Nat := 118140960795 + 3811619 * 2 ^ 59
def prefixEnd_3811619 : Nat := 4983230072969 + 3 ^ 40 * 3811619 * 2
def baseEnd_3811619 : Nat := 1957192618809827756833189

theorem tailTrace_3811619 : CollatzResearch.WordTrace tailWord_3811619 prefixEnd_3811619 1957192618809827756833189 := by
  unfold tailWord_3811619
  simp only [CollatzResearch.WordTrace]
  refine ⟨139021165978162810543725911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92680777318775207029150607 139021165978162810543725911)
  ·
    refine ⟨208531748967244215815588867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139021165978162810543725911 208531748967244215815588867)
    ·
      refine ⟨312797623450866323723383301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208531748967244215815588867 312797623450866323723383301)
      ·
        refine ⟨58649554397037435698134369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312797623450866323723383301 58649554397037435698134369)
        ·
          refine ⟨43987165797778076773600777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58649554397037435698134369 43987165797778076773600777)
          ·
            refine ⟨32990374348333557580200583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43987165797778076773600777 32990374348333557580200583)
            ·
              refine ⟨49485561522500336370300875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32990374348333557580200583 49485561522500336370300875)
              ·
                refine ⟨74228342283750504555451313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49485561522500336370300875 74228342283750504555451313)
                ·
                  refine ⟨55671256712812878416588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74228342283750504555451313 55671256712812878416588485)
                  ·
                    refine ⟨10438360633652414703110341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55671256712812878416588485 10438360633652414703110341)
                    ·
                      refine ⟨1957192618809827756833189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10438360633652414703110341 1957192618809827756833189)
                      ·
                        rfl

theorem cell23_3811619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3811619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811619 prefixEnd_3811619 := by exact prefixLift 3811619
  have htrace : WordTrace (prefixWord ++ tailWord_3811619) baseStart_3811619 baseEnd_3811619 := by
    simpa [prefixWord, tailWord_3811619, baseEnd_3811619] using wordTrace_append hprefix tailTrace_3811619
  have hstable : (prefixWord ++ tailWord_3811619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811619).length < 2 ^ (prefixWord ++ tailWord_3811619).sum := by decide
  have hdescent : baseEnd_3811619 < baseStart_3811619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811646 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3811646 : Nat := 118140960795 + 3811646 * 2 ^ 59
def prefixEnd_3811646 : Nat := 4983230072969 + 3 ^ 40 * 3811646 * 2
def baseEnd_3811646 : Nat := 217467386976388794577285

theorem tailTrace_3811646 : CollatzResearch.WordTrace tailWord_3811646 prefixEnd_3811646 217467386976388794577285 := by
  unfold tailWord_3811646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377768843633124269369849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92681433832709996103305861 17377768843633124269369849)
  ·
    refine ⟨13033326632724843202027387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17377768843633124269369849 13033326632724843202027387)
    ·
      refine ⟨19549989949087264803041081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13033326632724843202027387 19549989949087264803041081)
      ·
        refine ⟨14662492461815448602280811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19549989949087264803041081 14662492461815448602280811)
        ·
          refine ⟨21993738692723172903421217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14662492461815448602280811 21993738692723172903421217)
          ·
            refine ⟨16495304019542379677565913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21993738692723172903421217 16495304019542379677565913)
            ·
              refine ⟨12371478014656784758174435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495304019542379677565913 12371478014656784758174435)
              ·
                refine ⟨18557217021985177137261653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371478014656784758174435 18557217021985177137261653)
                ·
                  refine ⟨217467386976388794577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18557217021985177137261653 217467386976388794577285)
                  ·
                    rfl

theorem cell23_3811646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3811646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811646 prefixEnd_3811646 := by exact prefixLift 3811646
  have htrace : WordTrace (prefixWord ++ tailWord_3811646) baseStart_3811646 baseEnd_3811646 := by
    simpa [prefixWord, tailWord_3811646, baseEnd_3811646] using wordTrace_append hprefix tailTrace_3811646
  have hstable : (prefixWord ++ tailWord_3811646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811646).length < 2 ^ (prefixWord ++ tailWord_3811646).sum := by decide
  have hdescent : baseEnd_3811646 < baseStart_3811646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811707 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 1, 1, 3]
def baseStart_3811707 : Nat := 118140960795 + 3811707 * 2 ^ 59
def prefixEnd_3811707 : Nat := 4983230072969 + 3 ^ 40 * 3811707 * 2
def baseEnd_3811707 : Nat := 1957237805107423412532785

theorem tailTrace_3811707 : CollatzResearch.WordTrace tailWord_3811707 prefixEnd_3811707 1957237805107423412532785 := by
  unfold tailWord_3811707
  simp only [CollatzResearch.WordTrace]
  refine ⟨139024375601844001572929375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92682917067896001048619583 139024375601844001572929375)
  ·
    refine ⟨208536563402766002359394063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139024375601844001572929375 208536563402766002359394063)
    ·
      refine ⟨312804845104149003539091095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208536563402766002359394063 312804845104149003539091095)
      ·
        refine ⟨469207267656223505308636643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312804845104149003539091095 469207267656223505308636643)
        ·
          refine ⟨703810901484335257962954965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469207267656223505308636643 703810901484335257962954965)
          ·
            refine ⟨16495568003539107608506757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 703810901484335257962954965 16495568003539107608506757)
            ·
              refine ⟨3092919000663582676595017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16495568003539107608506757 3092919000663582676595017)
              ·
                refine ⟨2319689250497687007446263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092919000663582676595017 2319689250497687007446263)
                ·
                  refine ⟨3479533875746530511169395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319689250497687007446263 3479533875746530511169395)
                  ·
                    refine ⟨5219300813619795766754093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3479533875746530511169395 5219300813619795766754093)
                    ·
                      refine ⟨1957237805107423412532785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5219300813619795766754093 1957237805107423412532785)
                      ·
                        rfl

theorem cell23_3811707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 1, 1, 3].length) (baseStart_3811707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811707 prefixEnd_3811707 := by exact prefixLift 3811707
  have htrace : WordTrace (prefixWord ++ tailWord_3811707) baseStart_3811707 baseEnd_3811707 := by
    simpa [prefixWord, tailWord_3811707, baseEnd_3811707] using wordTrace_append hprefix tailTrace_3811707
  have hstable : (prefixWord ++ tailWord_3811707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811707).length < 2 ^ (prefixWord ++ tailWord_3811707).sum := by decide
  have hdescent : baseEnd_3811707 < baseStart_3811707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811713 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3811713 : Nat := 118140960795 + 3811713 * 2 ^ 59
def prefixEnd_3811713 : Nat := 4983230072969 + 3 ^ 40 * 3811713 * 2
def baseEnd_3811713 : Nat := 1957240885991350389057757

theorem tailTrace_3811713 : CollatzResearch.WordTrace tailWord_3811713 prefixEnd_3811713 1957240885991350389057757 := by
  unfold tailWord_3811713
  simp only [CollatzResearch.WordTrace]
  refine ⟨139024594439822264597647793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92683062959881509731765195 139024594439822264597647793)
  ·
    refine ⟨104268445829866698448235845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139024594439822264597647793 104268445829866698448235845)
    ·
      refine ⟨19550333593100005959044221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104268445829866698448235845 19550333593100005959044221)
      ·
        refine ⟨7331375097412502234641583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19550333593100005959044221 7331375097412502234641583)
        ·
          refine ⟨10997062646118753351962375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331375097412502234641583 10997062646118753351962375)
          ·
            refine ⟨16495593969178130027943563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997062646118753351962375 16495593969178130027943563)
            ·
              refine ⟨24743390953767195041915345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16495593969178130027943563 24743390953767195041915345)
              ·
                refine ⟨18557543215325396281436509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24743390953767195041915345 18557543215325396281436509)
                ·
                  refine ⟨6959078705747023605538691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18557543215325396281436509 6959078705747023605538691)
                  ·
                    refine ⟨10438618058620535408308037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959078705747023605538691 10438618058620535408308037)
                    ·
                      refine ⟨1957240885991350389057757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10438618058620535408308037 1957240885991350389057757)
                      ·
                        rfl

theorem cell23_3811713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3811713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811713 prefixEnd_3811713 := by exact prefixLift 3811713
  have htrace : WordTrace (prefixWord ++ tailWord_3811713) baseStart_3811713 baseEnd_3811713 := by
    simpa [prefixWord, tailWord_3811713, baseEnd_3811713] using wordTrace_append hprefix tailTrace_3811713
  have hstable : (prefixWord ++ tailWord_3811713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811713).length < 2 ^ (prefixWord ++ tailWord_3811713).sum := by decide
  have hdescent : baseEnd_3811713 < baseStart_3811713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811716 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3811716 : Nat := 118140960795 + 3811716 * 2 ^ 59
def prefixEnd_3811716 : Nat := 4983230072969 + 3 ^ 40 * 3811716 * 2
def baseEnd_3811716 : Nat := 1957242426433313877320243

theorem tailTrace_3811716 : CollatzResearch.WordTrace tailWord_3811716 prefixEnd_3811716 1957242426433313877320243 := by
  unfold tailWord_3811716
  simp only [CollatzResearch.WordTrace]
  refine ⟨69512351929405698055003501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92683135905874264073338001 69512351929405698055003501)
  ·
    refine ⟨26067131973527136770626313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69512351929405698055003501 26067131973527136770626313)
    ·
      refine ⟨19550348980145352577969735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26067131973527136770626313 19550348980145352577969735)
      ·
        refine ⟨29325523470218028866954603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19550348980145352577969735 29325523470218028866954603)
        ·
          refine ⟨43988285205327043300431905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29325523470218028866954603 43988285205327043300431905)
          ·
            refine ⟨32991213903995282475323929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43988285205327043300431905 32991213903995282475323929)
            ·
              refine ⟨24743410427996461856492947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32991213903995282475323929 24743410427996461856492947)
              ·
                refine ⟨37115115641994692784739421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24743410427996461856492947 37115115641994692784739421)
                ·
                  refine ⟨13918168365748009794277283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37115115641994692784739421 13918168365748009794277283)
                  ·
                    refine ⟨20877252548622014691415925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13918168365748009794277283 20877252548622014691415925)
                    ·
                      refine ⟨1957242426433313877320243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20877252548622014691415925 1957242426433313877320243)
                      ·
                        rfl

theorem cell23_3811716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3811716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811716 prefixEnd_3811716 := by exact prefixLift 3811716
  have htrace : WordTrace (prefixWord ++ tailWord_3811716) baseStart_3811716 baseEnd_3811716 := by
    simpa [prefixWord, tailWord_3811716, baseEnd_3811716] using wordTrace_append hprefix tailTrace_3811716
  have hstable : (prefixWord ++ tailWord_3811716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811716).length < 2 ^ (prefixWord ++ tailWord_3811716).sum := by decide
  have hdescent : baseEnd_3811716 < baseStart_3811716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811723 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 2, 4]
def baseStart_3811723 : Nat := 118140960795 + 3811723 * 2 ^ 59
def prefixEnd_3811723 : Nat := 4983230072969 + 3 ^ 40 * 3811723 * 2
def baseEnd_3811723 : Nat := 652415340265965116644237

theorem tailTrace_3811723 : CollatzResearch.WordTrace tailWord_3811723 prefixEnd_3811723 652415340265965116644237 := by
  unfold tailWord_3811723
  simp only [CollatzResearch.WordTrace]
  refine ⟨139024959169786036305511823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92683306113190690870341215 139024959169786036305511823)
  ·
    refine ⟨208537438754679054458267735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139024959169786036305511823 208537438754679054458267735)
    ·
      refine ⟨312806158132018581687401603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208537438754679054458267735 312806158132018581687401603)
      ·
        refine ⟨469209237198027872531102405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312806158132018581687401603 469209237198027872531102405)
        ·
          refine ⟨87976731974630226099581701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469209237198027872531102405 87976731974630226099581701)
          ·
            refine ⟨16495637245243167393671569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87976731974630226099581701 16495637245243167393671569)
            ·
              refine ⟨12371727933932375545253677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495637245243167393671569 12371727933932375545253677)
              ·
                refine ⟨4639397975224640829470129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12371727933932375545253677 4639397975224640829470129)
                ·
                  refine ⟨3479548481418480622102597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639397975224640829470129 3479548481418480622102597)
                  ·
                    refine ⟨652415340265965116644237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479548481418480622102597 652415340265965116644237)
                    ·
                      rfl

theorem cell23_3811723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 4].length) (baseStart_3811723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811723 prefixEnd_3811723 := by exact prefixLift 3811723
  have htrace : WordTrace (prefixWord ++ tailWord_3811723) baseStart_3811723 baseEnd_3811723 := by
    simpa [prefixWord, tailWord_3811723, baseEnd_3811723] using wordTrace_append hprefix tailTrace_3811723
  have hstable : (prefixWord ++ tailWord_3811723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811723).length < 2 ^ (prefixWord ++ tailWord_3811723).sum := by decide
  have hdescent : baseEnd_3811723 < baseStart_3811723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811733 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3811733 : Nat := 118140960795 + 3811733 * 2 ^ 59
def prefixEnd_3811733 : Nat := 4983230072969 + 3 ^ 40 * 3811733 * 2
def baseEnd_3811733 : Nat := 1957251155604440310807665

theorem tailTrace_3811733 : CollatzResearch.WordTrace tailWord_3811733 prefixEnd_3811733 1957251155604440310807665 := by
  unfold tailWord_3811733
  simp only [CollatzResearch.WordTrace]
  refine ⟨139025323899749808013375853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92683549266499872008917235 139025323899749808013375853)
  ·
    refine ⟨52134496462406178005015945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139025323899749808013375853 52134496462406178005015945)
    ·
      refine ⟨39100872346804633503761959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52134496462406178005015945 39100872346804633503761959)
      ·
        refine ⟨58651308520206950255642939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39100872346804633503761959 58651308520206950255642939)
        ·
          refine ⟨87976962780310425383464409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58651308520206950255642939 87976962780310425383464409)
          ·
            refine ⟨65982722085232819037598307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87976962780310425383464409 65982722085232819037598307)
            ·
              refine ⟨98974083127849228556397461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65982722085232819037598307 98974083127849228556397461)
              ·
                refine ⟨4639410146617932588581131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98974083127849228556397461 4639410146617932588581131)
                ·
                  refine ⟨6959115219926898882871697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639410146617932588581131 6959115219926898882871697)
                  ·
                    refine ⟨5219336414945174162153773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959115219926898882871697 5219336414945174162153773)
                    ·
                      refine ⟨1957251155604440310807665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5219336414945174162153773 1957251155604440310807665)
                      ·
                        rfl

theorem cell23_3811733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3811733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811733 prefixEnd_3811733 := by exact prefixLift 3811733
  have htrace : WordTrace (prefixWord ++ tailWord_3811733) baseStart_3811733 baseEnd_3811733 := by
    simpa [prefixWord, tailWord_3811733, baseEnd_3811733] using wordTrace_append hprefix tailTrace_3811733
  have hstable : (prefixWord ++ tailWord_3811733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811733).length < 2 ^ (prefixWord ++ tailWord_3811733).sum := by decide
  have hdescent : baseEnd_3811733 < baseStart_3811733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811747 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 1, 2, 2]
def baseStart_3811747 : Nat := 118140960795 + 3811747 * 2 ^ 59
def prefixEnd_3811747 : Nat := 4983230072969 + 3 ^ 40 * 3811747 * 2
def baseEnd_3811747 : Nat := 1957258344333603256032601

theorem tailTrace_3811747 : CollatzResearch.WordTrace tailWord_3811747 prefixEnd_3811747 1957258344333603256032601 := by
  unfold tailWord_3811747
  simp only [CollatzResearch.WordTrace]
  refine ⟨139025834521699088404385495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92683889681132725602923663 139025834521699088404385495)
  ·
    refine ⟨208538751782548632606578243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139025834521699088404385495 208538751782548632606578243)
    ·
      refine ⟨312808127673822948909867365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208538751782548632606578243 312808127673822948909867365)
      ·
        refine ⟨58651523938841802920600131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312808127673822948909867365 58651523938841802920600131)
        ·
          refine ⟨87977285908262704380900197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58651523938841802920600131 87977285908262704380900197)
          ·
            refine ⟨16495741107799257071418787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87977285908262704380900197 16495741107799257071418787)
            ·
              refine ⟨24743611661698885607128181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16495741107799257071418787 24743611661698885607128181)
              ·
                refine ⟨2319713593284270525668267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24743611661698885607128181 2319713593284270525668267)
                ·
                  refine ⟨3479570389926405788502401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319713593284270525668267 3479570389926405788502401)
                  ·
                    refine ⟨2609677792444804341376801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479570389926405788502401 2609677792444804341376801)
                    ·
                      refine ⟨1957258344333603256032601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609677792444804341376801 1957258344333603256032601)
                      ·
                        rfl

theorem cell23_3811747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_3811747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811747 prefixEnd_3811747 := by exact prefixLift 3811747
  have htrace : WordTrace (prefixWord ++ tailWord_3811747) baseStart_3811747 baseEnd_3811747 := by
    simpa [prefixWord, tailWord_3811747, baseEnd_3811747] using wordTrace_append hprefix tailTrace_3811747
  have hstable : (prefixWord ++ tailWord_3811747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811747).length < 2 ^ (prefixWord ++ tailWord_3811747).sum := by decide
  have hdescent : baseEnd_3811747 < baseStart_3811747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811777 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3811777 : Nat := 118140960795 + 3811777 * 2 ^ 59
def prefixEnd_3811777 : Nat := 4983230072969 + 3 ^ 40 * 3811777 * 2
def baseEnd_3811777 : Nat := 1957273748753238138657463

theorem tailTrace_3811777 : CollatzResearch.WordTrace tailWord_3811777 prefixEnd_3811777 1957273748753238138657463 := by
  unfold tailWord_3811777
  simp only [CollatzResearch.WordTrace]
  refine ⟨139026928711590403527977585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92684619141060269018651723 139026928711590403527977585)
  ·
    refine ⟨104270196533692802645983189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139026928711590403527977585 104270196533692802645983189)
    ·
      refine ⟨2443832731258425062015231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104270196533692802645983189 2443832731258425062015231)
      ·
        refine ⟨3665749096887637593022847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443832731258425062015231 3665749096887637593022847)
        ·
          refine ⟨5498623645331456389534271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665749096887637593022847 5498623645331456389534271)
          ·
            refine ⟨8247935467997184584301407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5498623645331456389534271 8247935467997184584301407)
            ·
              refine ⟨12371903201995776876452111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247935467997184584301407 12371903201995776876452111)
              ·
                refine ⟨18557854802993665314678167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371903201995776876452111 18557854802993665314678167)
                ·
                  refine ⟨27836782204490497972017251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18557854802993665314678167 27836782204490497972017251)
                  ·
                    refine ⟨41755173306735746958025877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27836782204490497972017251 41755173306735746958025877)
                    ·
                      refine ⟨1957273748753238138657463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41755173306735746958025877 1957273748753238138657463)
                      ·
                        rfl

theorem cell23_3811777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3811777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811777 prefixEnd_3811777 := by exact prefixLift 3811777
  have htrace : WordTrace (prefixWord ++ tailWord_3811777) baseStart_3811777 baseEnd_3811777 := by
    simpa [prefixWord, tailWord_3811777, baseEnd_3811777] using wordTrace_append hprefix tailTrace_3811777
  have hstable : (prefixWord ++ tailWord_3811777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811777).length < 2 ^ (prefixWord ++ tailWord_3811777).sum := by decide
  have hdescent : baseEnd_3811777 < baseStart_3811777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811820 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_3811820 : Nat := 118140960795 + 3811820 * 2 ^ 59
def prefixEnd_3811820 : Nat := 4983230072969 + 3 ^ 40 * 3811820 * 2
def baseEnd_3811820 : Nat := 1957295828421381470419765

theorem tailTrace_3811820 : CollatzResearch.WordTrace tailWord_3811820 prefixEnd_3811820 1957295828421381470419765 := by
  unfold tailWord_3811820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69514248525217310935896457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92685664700289747914528609 69514248525217310935896457)
  ·
    refine ⟨52135686393912983201922343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69514248525217310935896457 52135686393912983201922343)
    ·
      refine ⟨78203529590869474802883515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52135686393912983201922343 78203529590869474802883515)
      ·
        refine ⟨117305294386304212204325273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78203529590869474802883515 117305294386304212204325273)
        ·
          refine ⟨87978970789728159153243955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117305294386304212204325273 87978970789728159153243955)
          ·
            refine ⟨131968456184592238729865933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87978970789728159153243955 131968456184592238729865933)
            ·
              refine ⟨49488171069222089523699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131968456184592238729865933 49488171069222089523699725)
              ·
                refine ⟨18558064150958283571387397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49488171069222089523699725 18558064150958283571387397)
                ·
                  refine ⟨3479637028304678169635137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18558064150958283571387397 3479637028304678169635137)
                  ·
                    refine ⟨2609727771228508627226353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479637028304678169635137 2609727771228508627226353)
                    ·
                      refine ⟨1957295828421381470419765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609727771228508627226353 1957295828421381470419765)
                      ·
                        rfl

theorem cell23_3811820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_3811820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811820 prefixEnd_3811820 := by exact prefixLift 3811820
  have htrace : WordTrace (prefixWord ++ tailWord_3811820) baseStart_3811820 baseEnd_3811820 := by
    simpa [prefixWord, tailWord_3811820, baseEnd_3811820] using wordTrace_append hprefix tailTrace_3811820
  have hstable : (prefixWord ++ tailWord_3811820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811820).length < 2 ^ (prefixWord ++ tailWord_3811820).sum := by decide
  have hdescent : baseEnd_3811820 < baseStart_3811820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811837 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_3811837 : Nat := 118140960795 + 3811837 * 2 ^ 59
def prefixEnd_3811837 : Nat := 4983230072969 + 3 ^ 40 * 3811837 * 2
def baseEnd_3811837 : Nat := 1957304557592507903907187

theorem tailTrace_3811837 : CollatzResearch.WordTrace tailWord_3811837 prefixEnd_3811837 1957304557592507903907187 := by
  unfold tailWord_3811837
  simp only [CollatzResearch.WordTrace]
  refine ⟨139029117091373033775161765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92686078060915355850107843 139029117091373033775161765)
  ·
    refine ⟨26067959454632443832842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139029117091373033775161765 26067959454632443832842831)
    ·
      refine ⟨39101939181948665749264247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26067959454632443832842831 39101939181948665749264247)
      ·
        refine ⟨58652908772922998623896371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39101939181948665749264247 58652908772922998623896371)
        ·
          refine ⟨87979363159384497935844557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58652908772922998623896371 87979363159384497935844557)
          ·
            refine ⟨32992261184769186725941709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87979363159384497935844557 32992261184769186725941709)
            ·
              refine ⟨12372097944288445022228141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32992261184769186725941709 12372097944288445022228141)
              ·
                refine ⟨4639536729108166883335553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12372097944288445022228141 4639536729108166883335553)
                ·
                  refine ⟨3479652546831125162501665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639536729108166883335553 3479652546831125162501665)
                  ·
                    refine ⟨2609739410123343871876249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479652546831125162501665 2609739410123343871876249)
                    ·
                      refine ⟨1957304557592507903907187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609739410123343871876249 1957304557592507903907187)
                      ·
                        rfl

theorem cell23_3811837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_3811837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811837 prefixEnd_3811837 := by exact prefixLift 3811837
  have htrace : WordTrace (prefixWord ++ tailWord_3811837) baseStart_3811837 baseEnd_3811837 := by
    simpa [prefixWord, tailWord_3811837, baseEnd_3811837] using wordTrace_append hprefix tailTrace_3811837
  have hstable : (prefixWord ++ tailWord_3811837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811837).length < 2 ^ (prefixWord ++ tailWord_3811837).sum := by decide
  have hdescent : baseEnd_3811837 < baseStart_3811837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811873 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3811873 : Nat := 118140960795 + 3811873 * 2 ^ 59
def prefixEnd_3811873 : Nat := 4983230072969 + 3 ^ 40 * 3811873 * 2
def baseEnd_3811873 : Nat := 652441014298689921019007

theorem tailTrace_3811873 : CollatzResearch.WordTrace tailWord_3811873 prefixEnd_3811873 652441014298689921019007 := by
  unfold tailWord_3811873
  simp only [CollatzResearch.WordTrace]
  refine ⟨139030430119242611923472273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92686953412828407948981515 139030430119242611923472273)
  ·
    refine ⟨104272822589431958942604205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139030430119242611923472273 104272822589431958942604205)
    ·
      refine ⟨39102308471036984603476577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104272822589431958942604205 39102308471036984603476577)
      ·
        refine ⟨29326731353277738452607433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39102308471036984603476577 29326731353277738452607433)
        ·
          refine ⟨21995048514958303839455575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29326731353277738452607433 21995048514958303839455575)
          ·
            refine ⟨32992572772437455759183363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21995048514958303839455575 32992572772437455759183363)
            ·
              refine ⟨49488859158656183638775045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32992572772437455759183363 49488859158656183638775045)
              ·
                refine ⟨9279161092248034432270321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49488859158656183638775045 9279161092248034432270321)
                ·
                  refine ⟨6959370819186025824202741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279161092248034432270321 6959370819186025824202741)
                  ·
                    refine ⟨652441014298689921019007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6959370819186025824202741 652441014298689921019007)
                    ·
                      rfl

theorem cell23_3811873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3811873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811873 prefixEnd_3811873 := by exact prefixLift 3811873
  have htrace : WordTrace (prefixWord ++ tailWord_3811873) baseStart_3811873 baseEnd_3811873 := by
    simpa [prefixWord, tailWord_3811873, baseEnd_3811873] using wordTrace_append hprefix tailTrace_3811873
  have hstable : (prefixWord ++ tailWord_3811873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811873).length < 2 ^ (prefixWord ++ tailWord_3811873).sum := by decide
  have hdescent : baseEnd_3811873 < baseStart_3811873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811893 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3811893 : Nat := 118140960795 + 3811893 * 2 ^ 59
def prefixEnd_3811893 : Nat := 4983230072969 + 3 ^ 40 * 3811893 * 2
def baseEnd_3811893 : Nat := 1957333312509159684806929

theorem tailTrace_3811893 : CollatzResearch.WordTrace tailWord_3811893 prefixEnd_3811893 1957333312509159684806929 := by
  unfold tailWord_3811893
  simp only [CollatzResearch.WordTrace]
  refine ⟨139031159579170155339200333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92687439719446770226133555 139031159579170155339200333)
  ·
    refine ⟨52136684842188808252200125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139031159579170155339200333 52136684842188808252200125)
    ·
      refine ⟨19551256815820803094575047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52136684842188808252200125 19551256815820803094575047)
      ·
        refine ⟨29326885223731204641862571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19551256815820803094575047 29326885223731204641862571)
        ·
          refine ⟨43990327835596806962793857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29326885223731204641862571 43990327835596806962793857)
          ·
            refine ⟨32992745876697605222095393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43990327835596806962793857 32992745876697605222095393)
            ·
              refine ⟨24744559407523203916571545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32992745876697605222095393 24744559407523203916571545)
              ·
                refine ⟨18558419555642402937428659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24744559407523203916571545 18558419555642402937428659)
                ·
                  refine ⟨27837629333463604406142989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18558419555642402937428659 27837629333463604406142989)
                  ·
                    refine ⟨10439111000048851652303621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27837629333463604406142989 10439111000048851652303621)
                    ·
                      refine ⟨1957333312509159684806929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10439111000048851652303621 1957333312509159684806929)
                      ·
                        rfl

theorem cell23_3811893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3811893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811893 prefixEnd_3811893 := by exact prefixLift 3811893
  have htrace : WordTrace (prefixWord ++ tailWord_3811893) baseStart_3811893 baseEnd_3811893 := by
    simpa [prefixWord, tailWord_3811893, baseEnd_3811893] using wordTrace_append hprefix tailTrace_3811893
  have hstable : (prefixWord ++ tailWord_3811893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811893).length < 2 ^ (prefixWord ++ tailWord_3811893).sum := by decide
  have hdescent : baseEnd_3811893 < baseStart_3811893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811937 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3811937 : Nat := 118140960795 + 3811937 * 2 ^ 59
def prefixEnd_3811937 : Nat := 4983230072969 + 3 ^ 40 * 3811937 * 2
def baseEnd_3811937 : Nat := 652451968552652504218909

theorem tailTrace_3811937 : CollatzResearch.WordTrace tailWord_3811937 prefixEnd_3811937 652451968552652504218909 := by
  unfold tailWord_3811937
  simp only [CollatzResearch.WordTrace]
  refine ⟨139032764391010750853802065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92688509594007167235868043 139032764391010750853802065)
  ·
    refine ⟨104274573293258063140351549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139032764391010750853802065 104274573293258063140351549)
    ·
      refine ⟨39102964984971773677631831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104274573293258063140351549 39102964984971773677631831)
      ·
        refine ⟨58654447477457660516447747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39102964984971773677631831 58654447477457660516447747)
        ·
          refine ⟨87981671216186490774671621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58654447477457660516447747 87981671216186490774671621)
          ·
            refine ⟨16496563353034967020250929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87981671216186490774671621 16496563353034967020250929)
            ·
              refine ⟨12372422514776225265188197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496563353034967020250929 12372422514776225265188197)
              ·
                refine ⟨2319829221520542237222787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12372422514776225265188197 2319829221520542237222787)
                ·
                  refine ⟨3479743832280813355834181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319829221520542237222787 3479743832280813355834181)
                  ·
                    refine ⟨652451968552652504218909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479743832280813355834181 652451968552652504218909)
                    ·
                      rfl

theorem cell23_3811937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3811937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3811937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3811937 prefixEnd_3811937 := by exact prefixLift 3811937
  have htrace : WordTrace (prefixWord ++ tailWord_3811937) baseStart_3811937 baseEnd_3811937 := by
    simpa [prefixWord, tailWord_3811937, baseEnd_3811937] using wordTrace_append hprefix tailTrace_3811937
  have hstable : (prefixWord ++ tailWord_3811937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811937).length < 2 ^ (prefixWord ++ tailWord_3811937).sum := by decide
  have hdescent : baseEnd_3811937 < baseStart_3811937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812003 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3812003 : Nat := 118140960795 + 3812003 * 2 ^ 59
def prefixEnd_3812003 : Nat := 4983230072969 + 3 ^ 40 * 3812003 * 2
def baseEnd_3812003 : Nat := 1957389795381154254431423

theorem tailTrace_3812003 : CollatzResearch.WordTrace tailWord_3812003 prefixEnd_3812003 1957389795381154254431423 := by
  unfold tailWord_3812003
  simp only [CollatzResearch.WordTrace]
  refine ⟨139035171608771644125704663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92690114405847762750469775 139035171608771644125704663)
  ·
    refine ⟨208552757413157466188556995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139035171608771644125704663 208552757413157466188556995)
    ·
      refine ⟨312829136119736199282835493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208552757413157466188556995 312829136119736199282835493)
      ·
        refine ⟨58655463022450537365531655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312829136119736199282835493 58655463022450537365531655)
        ·
          refine ⟨87983194533675806048297483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58655463022450537365531655 87983194533675806048297483)
          ·
            refine ⟨131974791800513709072446225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87983194533675806048297483 131974791800513709072446225)
            ·
              refine ⟨98981093850385281804334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131974791800513709072446225 98981093850385281804334669)
              ·
                refine ⟨37117910193894480676625501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98981093850385281804334669 37117910193894480676625501)
                ·
                  refine ⟨13919216322710430253734563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37117910193894480676625501 13919216322710430253734563)
                  ·
                    refine ⟨20878824484065645380601845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13919216322710430253734563 20878824484065645380601845)
                    ·
                      refine ⟨1957389795381154254431423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20878824484065645380601845 1957389795381154254431423)
                      ·
                        rfl

theorem cell23_3812003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3812003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812003 prefixEnd_3812003 := by exact prefixLift 3812003
  have htrace : WordTrace (prefixWord ++ tailWord_3812003) baseStart_3812003 baseEnd_3812003 := by
    simpa [prefixWord, tailWord_3812003, baseEnd_3812003] using wordTrace_append hprefix tailTrace_3812003
  have hstable : (prefixWord ++ tailWord_3812003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812003).length < 2 ^ (prefixWord ++ tailWord_3812003).sum := by decide
  have hdescent : baseEnd_3812003 < baseStart_3812003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812014 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3812014 : Nat := 118140960795 + 3812014 * 2 ^ 59
def prefixEnd_3812014 : Nat := 4983230072969 + 3 ^ 40 * 3812014 * 2
def baseEnd_3812014 : Nat := 652465147889451237131291

theorem tailTrace_3812014 : CollatzResearch.WordTrace tailWord_3812014 prefixEnd_3812014 652465147889451237131291 := by
  unfold tailWord_3812014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379446601466474125544387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92690381874487862002903397 17379446601466474125544387)
  ·
    refine ⟨26069169902199711188316581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17379446601466474125544387 26069169902199711188316581)
    ·
      refine ⟨4887969356662445847809359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26069169902199711188316581 4887969356662445847809359)
      ·
        refine ⟨7331954034993668771714039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887969356662445847809359 7331954034993668771714039)
        ·
          refine ⟨10997931052490503157571059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331954034993668771714039 10997931052490503157571059)
          ·
            refine ⟨16496896578735754736356589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997931052490503157571059 16496896578735754736356589)
            ·
              refine ⟨6186336217025908026133721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16496896578735754736356589 6186336217025908026133721)
              ·
                refine ⟨4639752162769431019600291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186336217025908026133721 4639752162769431019600291)
                ·
                  refine ⟨6959628244154146529400437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639752162769431019600291 6959628244154146529400437)
                  ·
                    refine ⟨652465147889451237131291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6959628244154146529400437 652465147889451237131291)
                    ·
                      rfl

theorem cell23_3812014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3812014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812014 prefixEnd_3812014 := by exact prefixLift 3812014
  have htrace : WordTrace (prefixWord ++ tailWord_3812014) baseStart_3812014 baseEnd_3812014 := by
    simpa [prefixWord, tailWord_3812014, baseEnd_3812014] using wordTrace_append hprefix tailTrace_3812014
  have hstable : (prefixWord ++ tailWord_3812014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812014).length < 2 ^ (prefixWord ++ tailWord_3812014).sum := by decide
  have hdescent : baseEnd_3812014 < baseStart_3812014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812044 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_3812044 : Nat := 118140960795 + 3812044 * 2 ^ 59
def prefixEnd_3812044 : Nat := 4983230072969 + 3 ^ 40 * 3812044 * 2
def baseEnd_3812044 : Nat := 652470282695996198006245

theorem tailTrace_3812044 : CollatzResearch.WordTrace tailWord_3812044 prefixEnd_3812044 652470282695996198006245 := by
  unfold tailWord_3812044
  simp only [CollatzResearch.WordTrace]
  refine ⟨69518333500811554063973593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92691111334415405418631457 69518333500811554063973593)
  ·
    refine ⟨52138750125608665547980195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69518333500811554063973593 52138750125608665547980195)
    ·
      refine ⟨78208125188412998321970293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52138750125608665547980195 78208125188412998321970293)
      ·
        refine ⟨7332011736413718592684715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78208125188412998321970293 7332011736413718592684715)
        ·
          refine ⟨10998017604620577889027073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332011736413718592684715 10998017604620577889027073)
          ·
            refine ⟨8248513203465433416770305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998017604620577889027073 8248513203465433416770305)
            ·
              refine ⟨6186384902599075062577729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248513203465433416770305 6186384902599075062577729)
              ·
                refine ⟨4639788676949306296933297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186384902599075062577729 4639788676949306296933297)
                ·
                  refine ⟨3479841507711979722699973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639788676949306296933297 3479841507711979722699973)
                  ·
                    refine ⟨652470282695996198006245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3479841507711979722699973 652470282695996198006245)
                    ·
                      rfl

theorem cell23_3812044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_3812044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812044 prefixEnd_3812044 := by exact prefixLift 3812044
  have htrace : WordTrace (prefixWord ++ tailWord_3812044) baseStart_3812044 baseEnd_3812044 := by
    simpa [prefixWord, tailWord_3812044, baseEnd_3812044] using wordTrace_append hprefix tailTrace_3812044
  have hstable : (prefixWord ++ tailWord_3812044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812044).length < 2 ^ (prefixWord ++ tailWord_3812044).sum := by decide
  have hdescent : baseEnd_3812044 < baseStart_3812044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812067 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3812067 : Nat := 118140960795 + 3812067 * 2 ^ 59
def prefixEnd_3812067 : Nat := 4983230072969 + 3 ^ 40 * 3812067 * 2
def baseEnd_3812067 : Nat := 1957422658143042004031129

theorem tailTrace_3812067 : CollatzResearch.WordTrace tailWord_3812067 prefixEnd_3812067 1957422658143042004031129 := by
  unfold tailWord_3812067
  simp only [CollatzResearch.WordTrace]
  refine ⟨139037505880539783056034455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92691670587026522037356303 139037505880539783056034455)
  ·
    refine ⟨208556258820809674584051683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139037505880539783056034455 208556258820809674584051683)
    ·
      refine ⟨312834388231214511876077525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208556258820809674584051683 312834388231214511876077525)
      ·
        refine ⟨7332055974169090122095567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 312834388231214511876077525 7332055974169090122095567)
        ·
          refine ⟨10998083961253635183143351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332055974169090122095567 10998083961253635183143351)
          ·
            refine ⟨16497125941880452774715027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10998083961253635183143351 16497125941880452774715027)
            ·
              refine ⟨24745688912820679162072541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16497125941880452774715027 24745688912820679162072541)
              ·
                refine ⟨9279633342307754685777203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24745688912820679162072541 9279633342307754685777203)
                ·
                  refine ⟨13919450013461632028665805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279633342307754685777203 13919450013461632028665805)
                  ·
                    refine ⟨5219793755048112010749677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13919450013461632028665805 5219793755048112010749677)
                    ·
                      refine ⟨1957422658143042004031129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5219793755048112010749677 1957422658143042004031129)
                      ·
                        rfl

theorem cell23_3812067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3812067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812067 prefixEnd_3812067 := by exact prefixLift 3812067
  have htrace : WordTrace (prefixWord ++ tailWord_3812067) baseStart_3812067 baseEnd_3812067 := by
    simpa [prefixWord, tailWord_3812067, baseEnd_3812067] using wordTrace_append hprefix tailTrace_3812067
  have hstable : (prefixWord ++ tailWord_3812067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812067).length < 2 ^ (prefixWord ++ tailWord_3812067).sum := by decide
  have hdescent : baseEnd_3812067 < baseStart_3812067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812083 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 8]
def baseStart_3812083 : Nat := 118140960795 + 3812083 * 2 ^ 59
def prefixEnd_3812083 : Nat := 4983230072969 + 3 ^ 40 * 3812083 * 2
def baseEnd_3812083 : Nat := 652476957944504647143685

theorem tailTrace_3812083 : CollatzResearch.WordTrace tailWord_3812083 prefixEnd_3812083 652476957944504647143685 := by
  unfold tailWord_3812083
  simp only [CollatzResearch.WordTrace]
  refine ⟨139038089448481817788616903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92692059632321211859077935 139038089448481817788616903)
  ·
    refine ⟨208557134172722726682925355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139038089448481817788616903 208557134172722726682925355)
    ·
      refine ⟨312835701259084090024388033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208557134172722726682925355 312835701259084090024388033)
      ·
        refine ⟨234626775944313067518291025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312835701259084090024388033 234626775944313067518291025)
        ·
          refine ⟨175970081958234800638718269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234626775944313067518291025 175970081958234800638718269)
          ·
            refine ⟨65988780734338050239519351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175970081958234800638718269 65988780734338050239519351)
            ·
              refine ⟨98983171101507075359279027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65988780734338050239519351 98983171101507075359279027)
              ·
                refine ⟨148474756652260613038918541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98983171101507075359279027 148474756652260613038918541)
                ·
                  refine ⟨55678033744597729889594453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148474756652260613038918541 55678033744597729889594453)
                  ·
                    refine ⟨652476957944504647143685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55678033744597729889594453 652476957944504647143685)
                    ·
                      rfl

theorem cell23_3812083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_3812083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812083 prefixEnd_3812083 := by exact prefixLift 3812083
  have htrace : WordTrace (prefixWord ++ tailWord_3812083) baseStart_3812083 baseEnd_3812083 := by
    simpa [prefixWord, tailWord_3812083, baseEnd_3812083] using wordTrace_append hprefix tailTrace_3812083
  have hstable : (prefixWord ++ tailWord_3812083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812083).length < 2 ^ (prefixWord ++ tailWord_3812083).sum := by decide
  have hdescent : baseEnd_3812083 < baseStart_3812083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812085 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3812085 : Nat := 118140960795 + 3812085 * 2 ^ 59
def prefixEnd_3812085 : Nat := 4983230072969 + 3 ^ 40 * 3812085 * 2
def baseEnd_3812085 : Nat := 1957431900794822933606047

theorem tailTrace_3812085 : CollatzResearch.WordTrace tailWord_3812085 prefixEnd_3812085 1957431900794822933606047 := by
  unfold tailWord_3812085
  simp only [CollatzResearch.WordTrace]
  refine ⟨139038162394474572130189709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92692108262983048086793139 139038162394474572130189709)
  ·
    refine ⟨52139310897927964548821141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139038162394474572130189709 52139310897927964548821141)
    ·
      refine ⟨2444030198340373338225991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52139310897927964548821141 2444030198340373338225991)
      ·
        refine ⟨3666045297510560007338987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444030198340373338225991 3666045297510560007338987)
        ·
          refine ⟨5499067946265840011008481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666045297510560007338987 5499067946265840011008481)
          ·
            refine ⟨4124300959699380008256361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5499067946265840011008481 4124300959699380008256361)
            ·
              refine ⟨3093225719774535006192271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124300959699380008256361 3093225719774535006192271)
              ·
                refine ⟨4639838579661802509288407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093225719774535006192271 4639838579661802509288407)
                ·
                  refine ⟨6959757869492703763932611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639838579661802509288407 6959757869492703763932611)
                  ·
                    refine ⟨10439636804239055645898917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959757869492703763932611 10439636804239055645898917)
                    ·
                      refine ⟨1957431900794822933606047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10439636804239055645898917 1957431900794822933606047)
                      ·
                        rfl

theorem cell23_3812085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3812085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812085 prefixEnd_3812085 := by exact prefixLift 3812085
  have htrace : WordTrace (prefixWord ++ tailWord_3812085) baseStart_3812085 baseEnd_3812085 := by
    simpa [prefixWord, tailWord_3812085, baseEnd_3812085] using wordTrace_append hprefix tailTrace_3812085
  have hstable : (prefixWord ++ tailWord_3812085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812085).length < 2 ^ (prefixWord ++ tailWord_3812085).sum := by decide
  have hdescent : baseEnd_3812085 < baseStart_3812085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812100 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3812100 : Nat := 118140960795 + 3812100 * 2 ^ 59
def prefixEnd_3812100 : Nat := 4983230072969 + 3 ^ 40 * 3812100 * 2
def baseEnd_3812100 : Nat := 652479867668213458306159

theorem tailTrace_3812100 : CollatzResearch.WordTrace tailWord_3812100 prefixEnd_3812100 652479867668213458306159 := by
  unfold tailWord_3812100
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519354744710114845992877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92692472992946819794657169 69519354744710114845992877)
  ·
    refine ⟨26069758029266293067247329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69519354744710114845992877 26069758029266293067247329)
    ·
      refine ⟨19552318521949719800435497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26069758029266293067247329 19552318521949719800435497)
      ·
        refine ⟨14664238891462289850326623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19552318521949719800435497 14664238891462289850326623)
        ·
          refine ⟨21996358337193434775489935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14664238891462289850326623 21996358337193434775489935)
          ·
            refine ⟨32994537505790152163234903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21996358337193434775489935 32994537505790152163234903)
            ·
              refine ⟨49491806258685228244852355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32994537505790152163234903 49491806258685228244852355)
              ·
                refine ⟨74237709388027842367278533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49491806258685228244852355 74237709388027842367278533)
                ·
                  refine ⟨13919570510255220443864725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74237709388027842367278533 13919570510255220443864725)
                  ·
                    refine ⟨652479867668213458306159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13919570510255220443864725 652479867668213458306159)
                    ·
                      rfl

theorem cell23_3812100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3812100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812100 prefixEnd_3812100 := by exact prefixLift 3812100
  have htrace : WordTrace (prefixWord ++ tailWord_3812100) baseStart_3812100 baseEnd_3812100 := by
    simpa [prefixWord, tailWord_3812100, baseEnd_3812100] using wordTrace_append hprefix tailTrace_3812100
  have hstable : (prefixWord ++ tailWord_3812100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812100).length < 2 ^ (prefixWord ++ tailWord_3812100).sum := by decide
  have hdescent : baseEnd_3812100 < baseStart_3812100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3812110 : Nat := 118140960795 + 3812110 * 2 ^ 59
def prefixEnd_3812110 : Nat := 4983230072969 + 3 ^ 40 * 3812110 * 2
def baseEnd_3812110 : Nat := 1957444737811185335793431

theorem tailTrace_3812110 : CollatzResearch.WordTrace tailWord_3812110 prefixEnd_3812110 1957444737811185335793431 := by
  unfold tailWord_3812110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17379884277423000174981223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92692716146256000933233189 17379884277423000174981223)
  ·
    refine ⟨26069826416134500262471835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17379884277423000174981223 26069826416134500262471835)
    ·
      refine ⟨39104739624201750393707753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26069826416134500262471835 39104739624201750393707753)
      ·
        refine ⟨29328554718151312795280815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39104739624201750393707753 29328554718151312795280815)
        ·
          refine ⟨43992832077226969192921223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29328554718151312795280815 43992832077226969192921223)
          ·
            refine ⟨65989248115840453789381835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43992832077226969192921223 65989248115840453789381835)
            ·
              refine ⟨98983872173760680684072753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65989248115840453789381835 98983872173760680684072753)
              ·
                refine ⟨74237904130320510513054565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98983872173760680684072753 74237904130320510513054565)
                ·
                  refine ⟨13919607024435095721197731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74237904130320510513054565 13919607024435095721197731)
                  ·
                    refine ⟨20879410536652643581796597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13919607024435095721197731 20879410536652643581796597)
                    ·
                      refine ⟨1957444737811185335793431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20879410536652643581796597 1957444737811185335793431)
                      ·
                        rfl

theorem cell23_3812110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3812110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812110 prefixEnd_3812110 := by exact prefixLift 3812110
  have htrace : WordTrace (prefixWord ++ tailWord_3812110) baseStart_3812110 baseEnd_3812110 := by
    simpa [prefixWord, tailWord_3812110, baseEnd_3812110] using wordTrace_append hprefix tailTrace_3812110
  have hstable : (prefixWord ++ tailWord_3812110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812110).length < 2 ^ (prefixWord ++ tailWord_3812110).sum := by decide
  have hdescent : baseEnd_3812110 < baseStart_3812110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812124 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3812124 : Nat := 118140960795 + 3812124 * 2 ^ 59
def prefixEnd_3812124 : Nat := 4983230072969 + 3 ^ 40 * 3812124 * 2
def baseEnd_3812124 : Nat := 1957451926540348281018367

theorem tailTrace_3812124 : CollatzResearch.WordTrace tailWord_3812124 prefixEnd_3812124 1957451926540348281018367 := by
  unfold tailWord_3812124
  simp only [CollatzResearch.WordTrace]
  refine ⟨69519792420666640895429713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92693056560888854527239617 69519792420666640895429713)
  ·
    refine ⟨52139844315499980671572285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69519792420666640895429713 52139844315499980671572285)
    ·
      refine ⟨19552441618312492751839607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52139844315499980671572285 19552441618312492751839607)
      ·
        refine ⟨29328662427468739127759411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19552441618312492751839607 29328662427468739127759411)
        ·
          refine ⟨43992993641203108691639117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29328662427468739127759411 43992993641203108691639117)
          ·
            refine ⟨16497372615451165759364669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43992993641203108691639117 16497372615451165759364669)
            ·
              refine ⟨6186514730794187159761751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16497372615451165759364669 6186514730794187159761751)
              ·
                refine ⟨9279772096191280739642627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186514730794187159761751 9279772096191280739642627)
                ·
                  refine ⟨13919658144286921109463941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279772096191280739642627 13919658144286921109463941)
                  ·
                    refine ⟨2609935902053797708024489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13919658144286921109463941 2609935902053797708024489)
                    ·
                      refine ⟨1957451926540348281018367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609935902053797708024489 1957451926540348281018367)
                      ·
                        rfl

theorem cell23_3812124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3812124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812124 prefixEnd_3812124 := by exact prefixLift 3812124
  have htrace : WordTrace (prefixWord ++ tailWord_3812124) baseStart_3812124 baseEnd_3812124 := by
    simpa [prefixWord, tailWord_3812124, baseEnd_3812124] using wordTrace_append hprefix tailTrace_3812124
  have hstable : (prefixWord ++ tailWord_3812124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812124).length < 2 ^ (prefixWord ++ tailWord_3812124).sum := by decide
  have hdescent : baseEnd_3812124 < baseStart_3812124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812167 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_3812167 : Nat := 118140960795 + 3812167 * 2 ^ 59
def prefixEnd_3812167 : Nat := 4983230072969 + 3 ^ 40 * 3812167 * 2
def baseEnd_3812167 : Nat := 1957474006208491612780669

theorem tailTrace_3812167 : CollatzResearch.WordTrace tailWord_3812167 prefixEnd_3812167 1957474006208491612780669 := by
  unfold tailWord_3812167
  simp only [CollatzResearch.WordTrace]
  refine ⟨139041153180177500134674755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92694102120118333423116503 139041153180177500134674755)
  ·
    refine ⟨208561729770266250202012133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139041153180177500134674755 208561729770266250202012133)
    ·
      refine ⟨39105324331924921912877275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208561729770266250202012133 39105324331924921912877275)
      ·
        refine ⟨58657986497887382869315913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39105324331924921912877275 58657986497887382869315913)
        ·
          refine ⟨43993489873415537151986935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58657986497887382869315913 43993489873415537151986935)
          ·
            refine ⟨65990234810123305727980403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43993489873415537151986935 65990234810123305727980403)
            ·
              refine ⟨98985352215184958591970605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65990234810123305727980403 98985352215184958591970605)
              ·
                refine ⟨37119507080694359471988977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98985352215184958591970605 37119507080694359471988977)
                ·
                  refine ⟨27839630310520769603991733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37119507080694359471988977 27839630310520769603991733)
                  ·
                    refine ⟨2609965341611322150374225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27839630310520769603991733 2609965341611322150374225)
                    ·
                      refine ⟨1957474006208491612780669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2609965341611322150374225 1957474006208491612780669)
                      ·
                        rfl

theorem cell23_3812167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_3812167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812167 prefixEnd_3812167 := by exact prefixLift 3812167
  have htrace : WordTrace (prefixWord ++ tailWord_3812167) baseStart_3812167 baseEnd_3812167 := by
    simpa [prefixWord, tailWord_3812167, baseEnd_3812167] using wordTrace_append hprefix tailTrace_3812167
  have hstable : (prefixWord ++ tailWord_3812167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812167).length < 2 ^ (prefixWord ++ tailWord_3812167).sum := by decide
  have hdescent : baseEnd_3812167 < baseStart_3812167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812197 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3812197 : Nat := 118140960795 + 3812197 * 2 ^ 59
def prefixEnd_3812197 : Nat := 4983230072969 + 3 ^ 40 * 3812197 * 2
def baseEnd_3812197 : Nat := 1957489410628126495405531

theorem tailTrace_3812197 : CollatzResearch.WordTrace tailWord_3812197 prefixEnd_3812197 1957489410628126495405531 := by
  unfold tailWord_3812197
  simp only [CollatzResearch.WordTrace]
  refine ⟨139042247370068815258266845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92694831580045876838844563 139042247370068815258266845)
  ·
    refine ⟨52140842763775805721850067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139042247370068815258266845 52140842763775805721850067)
    ·
      refine ⟨78211264145663708582775101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52140842763775805721850067 78211264145663708582775101)
      ·
        refine ⟨29329224054623890718540663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78211264145663708582775101 29329224054623890718540663)
        ·
          refine ⟨43993836081935836077810995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29329224054623890718540663 43993836081935836077810995)
          ·
            refine ⟨65990754122903754116716493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43993836081935836077810995 65990754122903754116716493)
            ·
              refine ⟨24746532796088907793768685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65990754122903754116716493 24746532796088907793768685)
              ·
                refine ⟨9279949798533340422663257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24746532796088907793768685 9279949798533340422663257)
                ·
                  refine ⟨6959962348900005316997443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9279949798533340422663257 6959962348900005316997443)
                  ·
                    refine ⟨10439943523350007975496165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6959962348900005316997443 10439943523350007975496165)
                    ·
                      refine ⟨1957489410628126495405531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10439943523350007975496165 1957489410628126495405531)
                      ·
                        rfl

theorem cell23_3812197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3812197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812197 prefixEnd_3812197 := by exact prefixLift 3812197
  have htrace : WordTrace (prefixWord ++ tailWord_3812197) baseStart_3812197 baseEnd_3812197 := by
    simpa [prefixWord, tailWord_3812197, baseEnd_3812197] using wordTrace_append hprefix tailTrace_3812197
  have hstable : (prefixWord ++ tailWord_3812197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812197).length < 2 ^ (prefixWord ++ tailWord_3812197).sum := by decide
  have hdescent : baseEnd_3812197 < baseStart_3812197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812220 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 8]
def baseStart_3812220 : Nat := 118140960795 + 3812220 * 2 ^ 59
def prefixEnd_3812220 : Nat := 4983230072969 + 3 ^ 40 * 3812220 * 2
def baseEnd_3812220 : Nat := 217500135631464433935325

theorem tailTrace_3812220 : CollatzResearch.WordTrace tailWord_3812220 prefixEnd_3812220 217500135631464433935325 := by
  unfold tailWord_3812220
  simp only [CollatzResearch.WordTrace]
  refine ⟨69521543124492745093177057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92695390832656993457569409 69521543124492745093177057)
  ·
    refine ⟨52141157343369558819882793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69521543124492745093177057 52141157343369558819882793)
    ·
      refine ⟨39105868007527169114912095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52141157343369558819882793 39105868007527169114912095)
      ·
        refine ⟨58658802011290753672368143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39105868007527169114912095 58658802011290753672368143)
        ·
          refine ⟨87988203016936130508552215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58658802011290753672368143 87988203016936130508552215)
          ·
            refine ⟨131982304525404195762828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87988203016936130508552215 131982304525404195762828323)
            ·
              refine ⟨197973456788106293644242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131982304525404195762828323 197973456788106293644242485)
              ·
                refine ⟨18560011573884965029147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197973456788106293644242485 18560011573884965029147733)
                ·
                  refine ⟨217500135631464433935325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18560011573884965029147733 217500135631464433935325)
                  ·
                    rfl

theorem cell23_3812220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_3812220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812220 prefixEnd_3812220 := by exact prefixLift 3812220
  have htrace : WordTrace (prefixWord ++ tailWord_3812220) baseStart_3812220 baseEnd_3812220 := by
    simpa [prefixWord, tailWord_3812220, baseEnd_3812220] using wordTrace_append hprefix tailTrace_3812220
  have hstable : (prefixWord ++ tailWord_3812220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812220).length < 2 ^ (prefixWord ++ tailWord_3812220).sum := by decide
  have hdescent : baseEnd_3812220 < baseStart_3812220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812258 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3812258 : Nat := 118140960795 + 3812258 * 2 ^ 59
def prefixEnd_3812258 : Nat := 4983230072969 + 3 ^ 40 * 3812258 * 2
def baseEnd_3812258 : Nat := 652506910982683585580917

theorem tailTrace_3812258 : CollatzResearch.WordTrace tailWord_3812258 prefixEnd_3812258 652506910982683585580917 := by
  unfold tailWord_3812258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34761118055711955669059357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92696314815231881784158285 34761118055711955669059357)
  ·
    refine ⟨13035419270891983375897259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34761118055711955669059357 13035419270891983375897259)
    ·
      refine ⟨19553128906337975063845889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13035419270891983375897259 19553128906337975063845889)
      ·
        refine ⟨14664846679753481297884417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19553128906337975063845889 14664846679753481297884417)
        ·
          refine ⟨10998635009815110973413313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14664846679753481297884417 10998635009815110973413313)
          ·
            refine ⟨8248976257361333230059985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998635009815110973413313 8248976257361333230059985)
            ·
              refine ⟨6186732193020999922544989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8248976257361333230059985 6186732193020999922544989)
              ·
                refine ⟨2320024572382874970954371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186732193020999922544989 2320024572382874970954371)
                ·
                  refine ⟨3480036858574312456431557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320024572382874970954371 3480036858574312456431557)
                  ·
                    refine ⟨652506910982683585580917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480036858574312456431557 652506910982683585580917)
                    ·
                      rfl

theorem cell23_3812258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3812258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812258 prefixEnd_3812258 := by exact prefixLift 3812258
  have htrace : WordTrace (prefixWord ++ tailWord_3812258) baseStart_3812258 baseEnd_3812258 := by
    simpa [prefixWord, tailWord_3812258, baseEnd_3812258] using wordTrace_append hprefix tailTrace_3812258
  have hstable : (prefixWord ++ tailWord_3812258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812258).length < 2 ^ (prefixWord ++ tailWord_3812258).sum := by decide
  have hdescent : baseEnd_3812258 < baseStart_3812258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812267 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 1, 5]
def baseStart_3812267 : Nat := 118140960795 + 3812267 * 2 ^ 59
def prefixEnd_3812267 : Nat := 4983230072969 + 3 ^ 40 * 3812267 * 2
def baseEnd_3812267 : Nat := 652508451424647073843403

theorem tailTrace_3812267 : CollatzResearch.WordTrace tailWord_3812267 prefixEnd_3812267 652508451424647073843403 := by
  unfold tailWord_3812267
  simp only [CollatzResearch.WordTrace]
  refine ⟨139044800479815217213315055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92696533653210144808876703 139044800479815217213315055)
  ·
    refine ⟨208567200719722825819972583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139044800479815217213315055 208567200719722825819972583)
    ·
      refine ⟨312850801079584238729958875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208567200719722825819972583 312850801079584238729958875)
      ·
        refine ⟨469276201619376358094938313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312850801079584238729958875 469276201619376358094938313)
        ·
          refine ⟨351957151214532268571203735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469276201619376358094938313 351957151214532268571203735)
          ·
            refine ⟨527935726821798402856805603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351957151214532268571203735 527935726821798402856805603)
            ·
              refine ⟨791903590232697604285208405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527935726821798402856805603 791903590232697604285208405)
              ·
                refine ⟨4640060099019712525108643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 791903590232697604285208405 4640060099019712525108643)
                ·
                  refine ⟨6960090148529568787662965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640060099019712525108643 6960090148529568787662965)
                  ·
                    refine ⟨652508451424647073843403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6960090148529568787662965 652508451424647073843403)
                    ·
                      rfl

theorem cell23_3812267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 5].length) (baseStart_3812267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812267 prefixEnd_3812267 := by exact prefixLift 3812267
  have htrace : WordTrace (prefixWord ++ tailWord_3812267) baseStart_3812267 baseEnd_3812267 := by
    simpa [prefixWord, tailWord_3812267, baseEnd_3812267] using wordTrace_append hprefix tailTrace_3812267
  have hstable : (prefixWord ++ tailWord_3812267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812267).length < 2 ^ (prefixWord ++ tailWord_3812267).sum := by decide
  have hdescent : baseEnd_3812267 < baseStart_3812267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812281 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3812281 : Nat := 118140960795 + 3812281 * 2 ^ 59
def prefixEnd_3812281 : Nat := 4983230072969 + 3 ^ 40 * 3812281 * 2
def baseEnd_3812281 : Nat := 1957532543003104166755145

theorem tailTrace_3812281 : CollatzResearch.WordTrace tailWord_3812281 prefixEnd_3812281 1957532543003104166755145 := by
  unfold tailWord_3812281
  simp only [CollatzResearch.WordTrace]
  refine ⟨139045311101764497604324697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92696874067842998402883131 139045311101764497604324697)
  ·
    refine ⟨104283983326323373203243523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139045311101764497604324697 104283983326323373203243523)
    ·
      refine ⟨156425974989485059804865285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104283983326323373203243523 156425974989485059804865285)
      ·
        refine ⟨29329870310528448713412241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156425974989485059804865285 29329870310528448713412241)
        ·
          refine ⟨21997402732896336535059181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29329870310528448713412241 21997402732896336535059181)
          ·
            refine ⟨8249026024836126200647193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21997402732896336535059181 8249026024836126200647193)
            ·
              refine ⟨6186769518627094650485395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249026024836126200647193 6186769518627094650485395)
              ·
                refine ⟨9280154277940641975728093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186769518627094650485395 9280154277940641975728093)
                ·
                  refine ⟨3480057854227740740898035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9280154277940641975728093 3480057854227740740898035)
                  ·
                    refine ⟨5220086781341611111347053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480057854227740740898035 5220086781341611111347053)
                    ·
                      refine ⟨1957532543003104166755145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220086781341611111347053 1957532543003104166755145)
                      ·
                        rfl

theorem cell23_3812281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3812281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812281 prefixEnd_3812281 := by exact prefixLift 3812281
  have htrace : WordTrace (prefixWord ++ tailWord_3812281) baseStart_3812281 baseEnd_3812281 := by
    simpa [prefixWord, tailWord_3812281, baseEnd_3812281] using wordTrace_append hprefix tailTrace_3812281
  have hstable : (prefixWord ++ tailWord_3812281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812281).length < 2 ^ (prefixWord ++ tailWord_3812281).sum := by decide
  have hdescent : baseEnd_3812281 < baseStart_3812281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812287 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_3812287 : Nat := 118140960795 + 3812287 * 2 ^ 59
def prefixEnd_3812287 : Nat := 4983230072969 + 3 ^ 40 * 3812287 * 2
def baseEnd_3812287 : Nat := 1957535623887031143280117

theorem tailTrace_3812287 : CollatzResearch.WordTrace tailWord_3812287 prefixEnd_3812287 1957535623887031143280117 := by
  unfold tailWord_3812287
  simp only [CollatzResearch.WordTrace]
  refine ⟨139045529939742760629043115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92697019959828507086028743 139045529939742760629043115)
  ·
    refine ⟨208568294909614140943564673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139045529939742760629043115 208568294909614140943564673)
    ·
      refine ⟨156426221182210605707673505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208568294909614140943564673 156426221182210605707673505)
      ·
        refine ⟨117319665886657954280755129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156426221182210605707673505 117319665886657954280755129)
        ·
          refine ⟨87989749414993465710566347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117319665886657954280755129 87989749414993465710566347)
          ·
            refine ⟨131984624122490198565849521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87989749414993465710566347 131984624122490198565849521)
            ·
              refine ⟨98988468091867648924387141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131984624122490198565849521 98988468091867648924387141)
              ·
                refine ⟨18560337767225184173322589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98988468091867648924387141 18560337767225184173322589)
                ·
                  refine ⟨6960126662709444064995971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18560337767225184173322589 6960126662709444064995971)
                  ·
                    refine ⟨10440189994064166097493957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6960126662709444064995971 10440189994064166097493957)
                    ·
                      refine ⟨1957535623887031143280117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10440189994064166097493957 1957535623887031143280117)
                      ·
                        rfl

theorem cell23_3812287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_3812287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812287 prefixEnd_3812287 := by exact prefixLift 3812287
  have htrace : WordTrace (prefixWord ++ tailWord_3812287) baseStart_3812287 baseEnd_3812287 := by
    simpa [prefixWord, tailWord_3812287, baseEnd_3812287] using wordTrace_append hprefix tailTrace_3812287
  have hstable : (prefixWord ++ tailWord_3812287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812287).length < 2 ^ (prefixWord ++ tailWord_3812287).sum := by decide
  have hdescent : baseEnd_3812287 < baseStart_3812287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812297 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_3812297 : Nat := 118140960795 + 3812297 * 2 ^ 59
def prefixEnd_3812297 : Nat := 4983230072969 + 3 ^ 40 * 3812297 * 2
def baseEnd_3812297 : Nat := 652513586231192034718357

theorem tailTrace_3812297 : CollatzResearch.WordTrace tailWord_3812297 prefixEnd_3812297 652513586231192034718357 := by
  unfold tailWord_3812297
  simp only [CollatzResearch.WordTrace]
  refine ⟨139045894669706532336907145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92697263113137688224604763 139045894669706532336907145)
  ·
    refine ⟨104284421002279899252680359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139045894669706532336907145 104284421002279899252680359)
    ·
      refine ⟨156426631503419848879020539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104284421002279899252680359 156426631503419848879020539)
      ·
        refine ⟨234639947255129773318530809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156426631503419848879020539 234639947255129773318530809)
        ·
          refine ⟨175979960441347329988898107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234639947255129773318530809 175979960441347329988898107)
          ·
            refine ⟨263969940662020994983347161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175979960441347329988898107 263969940662020994983347161)
            ·
              refine ⟨197977455496515746237510371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263969940662020994983347161 197977455496515746237510371)
              ·
                refine ⟨296966183244773619356265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197977455496515746237510371 296966183244773619356265557)
                ·
                  refine ⟨3480072459899690851831237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 296966183244773619356265557 3480072459899690851831237)
                  ·
                    refine ⟨652513586231192034718357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480072459899690851831237 652513586231192034718357)
                    ·
                      rfl

theorem cell23_3812297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_3812297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812297 prefixEnd_3812297 := by exact prefixLift 3812297
  have htrace : WordTrace (prefixWord ++ tailWord_3812297) baseStart_3812297 baseEnd_3812297 := by
    simpa [prefixWord, tailWord_3812297, baseEnd_3812297] using wordTrace_append hprefix tailTrace_3812297
  have hstable : (prefixWord ++ tailWord_3812297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812297).length < 2 ^ (prefixWord ++ tailWord_3812297).sum := by decide
  have hdescent : baseEnd_3812297 < baseStart_3812297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812314 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_3812314 : Nat := 118140960795 + 3812314 * 2 ^ 59
def prefixEnd_3812314 : Nat := 4983230072969 + 3 ^ 40 * 3812314 * 2
def baseEnd_3812314 : Nat := 652516495954900845880831

theorem tailTrace_3812314 : CollatzResearch.WordTrace tailWord_3812314 prefixEnd_3812314 652516495954900845880831 := by
  unfold tailWord_3812314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34761628677661236060068999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92697676473763296160183997 34761628677661236060068999)
  ·
    refine ⟨52142443016491854090103499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34761628677661236060068999 52142443016491854090103499)
    ·
      refine ⟨78213664524737781135155249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52142443016491854090103499 78213664524737781135155249)
      ·
        refine ⟨58660248393553335851366437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78213664524737781135155249 58660248393553335851366437)
        ·
          refine ⟨10998796573791250472131207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58660248393553335851366437 10998796573791250472131207)
          ·
            refine ⟨16498194860686875708196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10998796573791250472131207 16498194860686875708196811)
            ·
              refine ⟨24747292291030313562295217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16498194860686875708196811 24747292291030313562295217)
              ·
                refine ⟨18560469218272735171721413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24747292291030313562295217 18560469218272735171721413)
                ·
                  refine ⟨3480087978426137844697765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18560469218272735171721413 3480087978426137844697765)
                  ·
                    refine ⟨652516495954900845880831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480087978426137844697765 652516495954900845880831)
                    ·
                      rfl

theorem cell23_3812314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_3812314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812314 prefixEnd_3812314 := by exact prefixLift 3812314
  have htrace : WordTrace (prefixWord ++ tailWord_3812314) baseStart_3812314 baseEnd_3812314 := by
    simpa [prefixWord, tailWord_3812314, baseEnd_3812314] using wordTrace_append hprefix tailTrace_3812314
  have hstable : (prefixWord ++ tailWord_3812314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812314).length < 2 ^ (prefixWord ++ tailWord_3812314).sum := by decide
  have hdescent : baseEnd_3812314 < baseStart_3812314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812327 : List Nat := [1, 1, 5, 2, 2, 1, 11]
def baseStart_3812327 : Nat := 118140960795 + 3812327 * 2 ^ 59
def prefixEnd_3812327 : Nat := 4983230072969 + 3 ^ 40 * 3812327 * 2
def baseEnd_3812327 : Nat := 24167360038434703540493

theorem tailTrace_3812327 : CollatzResearch.WordTrace tailWord_3812327 prefixEnd_3812327 24167360038434703540493 := by
  unfold tailWord_3812327
  simp only [CollatzResearch.WordTrace]
  refine ⟨139046988859597847460499235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92697992573065231640332823 139046988859597847460499235)
  ·
    refine ⟨208570483289396771190748853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139046988859597847460499235 208570483289396771190748853)
    ·
      refine ⟨19553482808380947299132705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208570483289396771190748853 19553482808380947299132705)
      ·
        refine ⟨14665112106285710474349529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19553482808380947299132705 14665112106285710474349529)
        ·
          refine ⟨10998834079714282855762147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14665112106285710474349529 10998834079714282855762147)
          ·
            refine ⟨16498251119571424283643221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10998834079714282855762147 16498251119571424283643221)
            ·
              refine ⟨24167360038434703540493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16498251119571424283643221 24167360038434703540493)
              ·
                rfl

theorem cell23_3812327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 11].length) (baseStart_3812327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812327 prefixEnd_3812327 := by exact prefixLift 3812327
  have htrace : WordTrace (prefixWord ++ tailWord_3812327) baseStart_3812327 baseEnd_3812327 := by
    simpa [prefixWord, tailWord_3812327, baseEnd_3812327] using wordTrace_append hprefix tailTrace_3812327
  have hstable : (prefixWord ++ tailWord_3812327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812327).length < 2 ^ (prefixWord ++ tailWord_3812327).sum := by decide
  have hdescent : baseEnd_3812327 < baseStart_3812327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812348 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_3812348 : Nat := 118140960795 + 3812348 * 2 ^ 59
def prefixEnd_3812348 : Nat := 4983230072969 + 3 ^ 40 * 3812348 * 2
def baseEnd_3812348 : Nat := 652522315402318468205779

theorem tailTrace_3812348 : CollatzResearch.WordTrace tailWord_3812348 prefixEnd_3812348 652522315402318468205779 := by
  unfold tailWord_3812348
  simp only [CollatzResearch.WordTrace]
  refine ⟨69523877396260884023506849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92698503195014512031342465 69523877396260884023506849)
  ·
    refine ⟨52142908047195663017630137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69523877396260884023506849 52142908047195663017630137)
    ·
      refine ⟨39107181035396747263222603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52142908047195663017630137 39107181035396747263222603)
      ·
        refine ⟨58660771553095120894833905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39107181035396747263222603 58660771553095120894833905)
        ·
          refine ⟨43995578664821340671125429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58660771553095120894833905 43995578664821340671125429)
          ·
            refine ⟨4124585499827000687918009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43995578664821340671125429 4124585499827000687918009)
            ·
              refine ⟨3093439124870250515938507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124585499827000687918009 3093439124870250515938507)
              ·
                refine ⟨4640158687305375773907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093439124870250515938507 4640158687305375773907761)
                ·
                  refine ⟨3480119015479031830430821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640158687305375773907761 3480119015479031830430821)
                  ·
                    refine ⟨652522315402318468205779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480119015479031830430821 652522315402318468205779)
                    ·
                      rfl

theorem cell23_3812348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_3812348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812348 prefixEnd_3812348 := by exact prefixLift 3812348
  have htrace : WordTrace (prefixWord ++ tailWord_3812348) baseStart_3812348 baseEnd_3812348 := by
    simpa [prefixWord, tailWord_3812348, baseEnd_3812348] using wordTrace_append hprefix tailTrace_3812348
  have hstable : (prefixWord ++ tailWord_3812348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812348).length < 2 ^ (prefixWord ++ tailWord_3812348).sum := by decide
  have hdescent : baseEnd_3812348 < baseStart_3812348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812388 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3812388 : Nat := 118140960795 + 3812388 * 2 ^ 59
def prefixEnd_3812388 : Nat := 4983230072969 + 3 ^ 40 * 3812388 * 2
def baseEnd_3812388 : Nat := 1957587485433135248117153

theorem tailTrace_3812388 : CollatzResearch.WordTrace tailWord_3812388 prefixEnd_3812388 1957587485433135248117153 := by
  unfold tailWord_3812388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69524606856188427439234909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92699475808251236585646545 69524606856188427439234909)
  ·
    refine ⟨26071727571070660289713091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69524606856188427439234909 26071727571070660289713091)
    ·
      refine ⟨39107591356605990434569637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26071727571070660289713091 39107591356605990434569637)
      ·
        refine ⟨7332673379363623206481807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39107591356605990434569637 7332673379363623206481807)
        ·
          refine ⟨10999010069045434809722711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332673379363623206481807 10999010069045434809722711)
          ·
            refine ⟨16498515103568152214584067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10999010069045434809722711 16498515103568152214584067)
            ·
              refine ⟨24747772655352228321876101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16498515103568152214584067 24747772655352228321876101)
              ·
                refine ⟨4640207372878542810351769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24747772655352228321876101 4640207372878542810351769)
                ·
                  refine ⟨3480155529658907107763827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640207372878542810351769 3480155529658907107763827)
                  ·
                    refine ⟨5220233294488360661645741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480155529658907107763827 5220233294488360661645741)
                    ·
                      refine ⟨1957587485433135248117153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220233294488360661645741 1957587485433135248117153)
                      ·
                        rfl

theorem cell23_3812388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3812388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812388 prefixEnd_3812388 := by exact prefixLift 3812388
  have htrace : WordTrace (prefixWord ++ tailWord_3812388) baseStart_3812388 baseEnd_3812388 := by
    simpa [prefixWord, tailWord_3812388, baseEnd_3812388] using wordTrace_append hprefix tailTrace_3812388
  have hstable : (prefixWord ++ tailWord_3812388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812388).length < 2 ^ (prefixWord ++ tailWord_3812388).sum := by decide
  have hdescent : baseEnd_3812388 < baseStart_3812388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812461 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3812461 : Nat := 118140960795 + 3812461 * 2 ^ 59
def prefixEnd_3812461 : Nat := 4983230072969 + 3 ^ 40 * 3812461 * 2
def baseEnd_3812461 : Nat := 1957624969520913462504317

theorem tailTrace_3812461 : CollatzResearch.WordTrace tailWord_3812461 prefixEnd_3812461 1957624969520913462504317 := by
  unfold tailWord_3812461
  simp only [CollatzResearch.WordTrace]
  refine ⟨139051876241112388345877237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92701250827408258897251491 139051876241112388345877237)
  ·
    refine ⟨13036113397604286407425991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139051876241112388345877237 13036113397604286407425991)
    ·
      refine ⟨19554170096406429611138987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036113397604286407425991 19554170096406429611138987)
      ·
        refine ⟨29331255144609644416708481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19554170096406429611138987 29331255144609644416708481)
        ·
          refine ⟨21998441358457233312531361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29331255144609644416708481 21998441358457233312531361)
          ·
            refine ⟨16498831018842924984398521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21998441358457233312531361 16498831018842924984398521)
            ·
              refine ⟨12374123264132193738298891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16498831018842924984398521 12374123264132193738298891)
              ·
                refine ⟨18561184896198290607448337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12374123264132193738298891 18561184896198290607448337)
                ·
                  refine ⟨13920888672148717955586253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18561184896198290607448337 13920888672148717955586253)
                  ·
                    refine ⟨5220333252055769233344845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13920888672148717955586253 5220333252055769233344845)
                    ·
                      refine ⟨1957624969520913462504317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220333252055769233344845 1957624969520913462504317)
                      ·
                        rfl

theorem cell23_3812461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3812461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812461 prefixEnd_3812461 := by exact prefixLift 3812461
  have htrace : WordTrace (prefixWord ++ tailWord_3812461) baseStart_3812461 baseEnd_3812461 := by
    simpa [prefixWord, tailWord_3812461, baseEnd_3812461] using wordTrace_append hprefix tailTrace_3812461
  have hstable : (prefixWord ++ tailWord_3812461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812461).length < 2 ^ (prefixWord ++ tailWord_3812461).sum := by decide
  have hdescent : baseEnd_3812461 < baseStart_3812461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812462 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3812462 : Nat := 118140960795 + 3812462 * 2 ^ 59
def prefixEnd_3812462 : Nat := 4983230072969 + 3 ^ 40 * 3812462 * 2
def baseEnd_3812462 : Nat := 1957625483001567958591813

theorem tailTrace_3812462 : CollatzResearch.WordTrace tailWord_3812462 prefixEnd_3812462 1957625483001567958591813 := by
  unfold tailWord_3812462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381489089263595689582955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92701275142739177011109093 17381489089263595689582955)
  ·
    refine ⟨26072233633895393534374433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17381489089263595689582955 26072233633895393534374433)
    ·
      refine ⟨19554175225421545150780825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26072233633895393534374433 19554175225421545150780825)
      ·
        refine ⟨14665631419066158863085619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19554175225421545150780825 14665631419066158863085619)
        ·
          refine ⟨21998447128599238294628429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665631419066158863085619 21998447128599238294628429)
          ·
            refine ⟨8249417673224714360485661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21998447128599238294628429 8249417673224714360485661)
            ·
              refine ⟨3093531627459267885182123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8249417673224714360485661 3093531627459267885182123)
              ·
                refine ⟨4640297441188901827773185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093531627459267885182123 4640297441188901827773185)
                ·
                  refine ⟨3480223080891676370829889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640297441188901827773185 3480223080891676370829889)
                  ·
                    refine ⟨2610167310668757278122417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480223080891676370829889 2610167310668757278122417)
                    ·
                      refine ⟨1957625483001567958591813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610167310668757278122417 1957625483001567958591813)
                      ·
                        rfl

theorem cell23_3812462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3812462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812462 prefixEnd_3812462 := by exact prefixLift 3812462
  have htrace : WordTrace (prefixWord ++ tailWord_3812462) baseStart_3812462 baseEnd_3812462 := by
    simpa [prefixWord, tailWord_3812462, baseEnd_3812462] using wordTrace_append hprefix tailTrace_3812462
  have hstable : (prefixWord ++ tailWord_3812462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812462).length < 2 ^ (prefixWord ++ tailWord_3812462).sum := by decide
  have hdescent : baseEnd_3812462 < baseStart_3812462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812485 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 5]
def baseStart_3812485 : Nat := 118140960795 + 3812485 * 2 ^ 59
def prefixEnd_3812485 : Nat := 4983230072969 + 3 ^ 40 * 3812485 * 2
def baseEnd_3812485 : Nat := 217515254784069040956023

theorem tailTrace_3812485 : CollatzResearch.WordTrace tailWord_3812485 prefixEnd_3812485 217515254784069040956023 := by
  unfold tailWord_3812485
  simp only [CollatzResearch.WordTrace]
  refine ⟨139052751593025440444750909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92701834395350293629833939 139052751593025440444750909)
  ·
    refine ⟨52144781847384540166781591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139052751593025440444750909 52144781847384540166781591)
    ·
      refine ⟨78217172771076810250172387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52144781847384540166781591 78217172771076810250172387)
      ·
        refine ⟨117325759156615215375258581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78217172771076810250172387 117325759156615215375258581)
        ·
          refine ⟨2749822480233169110357623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117325759156615215375258581 2749822480233169110357623)
          ·
            refine ⟨4124733720349753665536435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749822480233169110357623 4124733720349753665536435)
            ·
              refine ⟨6187100580524630498304653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124733720349753665536435 6187100580524630498304653)
              ·
                refine ⟨2320162717696736436864245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6187100580524630498304653 2320162717696736436864245)
                ·
                  refine ⟨217515254784069040956023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320162717696736436864245 217515254784069040956023)
                  ·
                    rfl

theorem cell23_3812485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_3812485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812485 prefixEnd_3812485 := by exact prefixLift 3812485
  have htrace : WordTrace (prefixWord ++ tailWord_3812485) baseStart_3812485 baseEnd_3812485 := by
    simpa [prefixWord, tailWord_3812485, baseEnd_3812485] using wordTrace_append hprefix tailTrace_3812485
  have hstable : (prefixWord ++ tailWord_3812485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812485).length < 2 ^ (prefixWord ++ tailWord_3812485).sum := by decide
  have hdescent : baseEnd_3812485 < baseStart_3812485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812501 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_3812501 : Nat := 118140960795 + 3812501 * 2 ^ 59
def prefixEnd_3812501 : Nat := 4983230072969 + 3 ^ 40 * 3812501 * 2
def baseEnd_3812501 : Nat := 1957645508747093306004133

theorem tailTrace_3812501 : CollatzResearch.WordTrace tailWord_3812501 prefixEnd_3812501 1957645508747093306004133 := by
  unfold tailWord_3812501
  simp only [CollatzResearch.WordTrace]
  refine ⟨139053335160967475177333357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92702223440644983451555571 139053335160967475177333357)
  ·
    refine ⟨52145000685362803191500009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139053335160967475177333357 52145000685362803191500009)
    ·
      refine ⟨39108750514022102393625007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52145000685362803191500009 39108750514022102393625007)
      ·
        refine ⟨58663125771033153590437511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39108750514022102393625007 58663125771033153590437511)
        ·
          refine ⟨87994688656549730385656267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58663125771033153590437511 87994688656549730385656267)
          ·
            refine ⟨131992032984824595578484401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87994688656549730385656267 131992032984824595578484401)
            ·
              refine ⟨98994024738618446683863301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131992032984824595578484401 98994024738618446683863301)
              ·
                refine ⟨18561379638490958753224369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98994024738618446683863301 18561379638490958753224369)
                ·
                  refine ⟨13921034728868219064918277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18561379638490958753224369 13921034728868219064918277)
                  ·
                    refine ⟨2610194011662791074672177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13921034728868219064918277 2610194011662791074672177)
                    ·
                      refine ⟨1957645508747093306004133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610194011662791074672177 1957645508747093306004133)
                      ·
                        rfl

theorem cell23_3812501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_3812501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812501 prefixEnd_3812501 := by exact prefixLift 3812501
  have htrace : WordTrace (prefixWord ++ tailWord_3812501) baseStart_3812501 baseEnd_3812501 := by
    simpa [prefixWord, tailWord_3812501, baseEnd_3812501] using wordTrace_append hprefix tailTrace_3812501
  have hstable : (prefixWord ++ tailWord_3812501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812501).length < 2 ^ (prefixWord ++ tailWord_3812501).sum := by decide
  have hdescent : baseEnd_3812501 < baseStart_3812501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812558 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_3812558 : Nat := 118140960795 + 3812558 * 2 ^ 59
def prefixEnd_3812558 : Nat := 4983230072969 + 3 ^ 40 * 3812558 * 2
def baseEnd_3812558 : Nat := 217519419682711064776819

theorem tailTrace_3812558 : CollatzResearch.WordTrace tailWord_3812558 prefixEnd_3812558 217519419682711064776819 := by
  unfold tailWord_3812558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381926765220121739019791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92703609414507315941438885 17381926765220121739019791)
  ·
    refine ⟨26072890147830182608529687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17381926765220121739019791 26072890147830182608529687)
    ·
      refine ⟨39109335221745273912794531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26072890147830182608529687 39109335221745273912794531)
      ·
        refine ⟨58664002832617910869191797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39109335221745273912794531 58664002832617910869191797)
        ·
          refine ⟨5499750265557929143986731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58664002832617910869191797 5499750265557929143986731)
          ·
            refine ⟨8249625398336893715980097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499750265557929143986731 8249625398336893715980097)
            ·
              refine ⟨6187219048752670286985073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249625398336893715980097 6187219048752670286985073)
              ·
                refine ⟨4640414286564502715238805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187219048752670286985073 4640414286564502715238805)
                ·
                  refine ⟨217519419682711064776819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4640414286564502715238805 217519419682711064776819)
                  ·
                    rfl

theorem cell23_3812558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_3812558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812558 prefixEnd_3812558 := by exact prefixLift 3812558
  have htrace : WordTrace (prefixWord ++ tailWord_3812558) baseStart_3812558 baseEnd_3812558 := by
    simpa [prefixWord, tailWord_3812558, baseEnd_3812558] using wordTrace_append hprefix tailTrace_3812558
  have hstable : (prefixWord ++ tailWord_3812558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812558).length < 2 ^ (prefixWord ++ tailWord_3812558).sum := by decide
  have hdescent : baseEnd_3812558 < baseStart_3812558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812561 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_3812561 : Nat := 118140960795 + 3812561 * 2 ^ 59
def prefixEnd_3812561 : Nat := 4983230072969 + 3 ^ 40 * 3812561 * 2
def baseEnd_3812561 : Nat := 1957676317586363071253857

theorem tailTrace_3812561 : CollatzResearch.WordTrace tailWord_3812561 prefixEnd_3812561 1957676317586363071253857 := by
  unfold tailWord_3812561
  simp only [CollatzResearch.WordTrace]
  refine ⟨139055523540750105424517537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92703682360500070283011691 139055523540750105424517537)
  ·
    refine ⟨104291642655562579068388153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139055523540750105424517537 104291642655562579068388153)
    ·
      refine ⟨78218731991671934301291115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104291642655562579068388153 78218731991671934301291115)
      ·
        refine ⟨117328097987507901451936673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78218731991671934301291115 117328097987507901451936673)
        ·
          refine ⟨87996073490630926088952505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117328097987507901451936673 87996073490630926088952505)
          ·
            refine ⟨65997055117973194566714379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87996073490630926088952505 65997055117973194566714379)
            ·
              refine ⟨98995582676959791850071569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65997055117973194566714379 98995582676959791850071569)
              ·
                refine ⟨74246687007719843887553677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98995582676959791850071569 74246687007719843887553677)
                ·
                  refine ⟨27842507627894941457832629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74246687007719843887553677 27842507627894941457832629)
                  ·
                    refine ⟨2610235090115150761671809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27842507627894941457832629 2610235090115150761671809)
                    ·
                      refine ⟨1957676317586363071253857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610235090115150761671809 1957676317586363071253857)
                      ·
                        rfl

theorem cell23_3812561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_3812561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812561 prefixEnd_3812561 := by exact prefixLift 3812561
  have htrace : WordTrace (prefixWord ++ tailWord_3812561) baseStart_3812561 baseEnd_3812561 := by
    simpa [prefixWord, tailWord_3812561, baseEnd_3812561] using wordTrace_append hprefix tailTrace_3812561
  have hstable : (prefixWord ++ tailWord_3812561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812561).length < 2 ^ (prefixWord ++ tailWord_3812561).sum := by decide
  have hdescent : baseEnd_3812561 < baseStart_3812561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812595 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 2, 3, 2]
def baseStart_3812595 : Nat := 118140960795 + 3812595 * 2 ^ 59
def prefixEnd_3812595 : Nat := 4983230072969 + 3 ^ 40 * 3812595 * 2
def baseEnd_3812595 : Nat := 1957693775928615938228701

theorem tailTrace_3812595 : CollatzResearch.WordTrace tailWord_3812595 prefixEnd_3812595 1957693775928615938228701 := by
  unfold tailWord_3812595
  simp only [CollatzResearch.WordTrace]
  refine ⟨139056763622626929231255239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92704509081751286154170159 139056763622626929231255239)
  ·
    refine ⟨208585145433940393846882859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139056763622626929231255239 208585145433940393846882859)
    ·
      refine ⟨312877718150910590770324289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208585145433940393846882859 312877718150910590770324289)
      ·
        refine ⟨234658288613182943077743217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312877718150910590770324289 234658288613182943077743217)
        ·
          refine ⟨175993716459887207308307413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234658288613182943077743217 175993716459887207308307413)
          ·
            refine ⟨4124852729528606421288455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175993716459887207308307413 4124852729528606421288455)
            ·
              refine ⟨6187279094292909631932683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124852729528606421288455 6187279094292909631932683)
              ·
                refine ⟨9280918641439364447899025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187279094292909631932683 9280918641439364447899025)
                ·
                  refine ⟨6960688981079523335924269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9280918641439364447899025 6960688981079523335924269)
                  ·
                    refine ⟨2610258367904821250971601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6960688981079523335924269 2610258367904821250971601)
                    ·
                      refine ⟨1957693775928615938228701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610258367904821250971601 1957693775928615938228701)
                      ·
                        rfl

theorem cell23_3812595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3, 2].length) (baseStart_3812595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812595 prefixEnd_3812595 := by exact prefixLift 3812595
  have htrace : WordTrace (prefixWord ++ tailWord_3812595) baseStart_3812595 baseEnd_3812595 := by
    simpa [prefixWord, tailWord_3812595, baseEnd_3812595] using wordTrace_append hprefix tailTrace_3812595
  have hstable : (prefixWord ++ tailWord_3812595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812595).length < 2 ^ (prefixWord ++ tailWord_3812595).sum := by decide
  have hdescent : baseEnd_3812595 < baseStart_3812595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812596 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3812596 : Nat := 118140960795 + 3812596 * 2 ^ 59
def prefixEnd_3812596 : Nat := 4983230072969 + 3 ^ 40 * 3812596 * 2
def baseEnd_3812596 : Nat := 652564763136423478105399

theorem tailTrace_3812596 : CollatzResearch.WordTrace tailWord_3812596 prefixEnd_3812596 652564763136423478105399 := by
  unfold tailWord_3812596
  simp only [CollatzResearch.WordTrace]
  refine ⟨69528400047811653201020821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92704533397082204268027761 69528400047811653201020821)
  ·
    refine ⟨3259143752241171243797851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69528400047811653201020821 3259143752241171243797851)
    ·
      refine ⟨4888715628361756865696777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259143752241171243797851 4888715628361756865696777)
      ·
        refine ⟨3666536721271317649272583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4888715628361756865696777 3666536721271317649272583)
        ·
          refine ⟨5499805081906976473908875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666536721271317649272583 5499805081906976473908875)
          ·
            refine ⟨8249707622860464710863313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499805081906976473908875 8249707622860464710863313)
            ·
              refine ⟨6187280717145348533147485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249707622860464710863313 6187280717145348533147485)
              ·
                refine ⟨2320230268929505699930307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6187280717145348533147485 2320230268929505699930307)
                ·
                  refine ⟨3480345403394258549895461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320230268929505699930307 3480345403394258549895461)
                  ·
                    refine ⟨652564763136423478105399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480345403394258549895461 652564763136423478105399)
                    ·
                      rfl

theorem cell23_3812596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3812596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812596 prefixEnd_3812596 := by exact prefixLift 3812596
  have htrace : WordTrace (prefixWord ++ tailWord_3812596) baseStart_3812596 baseEnd_3812596 := by
    simpa [prefixWord, tailWord_3812596, baseEnd_3812596] using wordTrace_append hprefix tailTrace_3812596
  have hstable : (prefixWord ++ tailWord_3812596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812596).length < 2 ^ (prefixWord ++ tailWord_3812596).sum := by decide
  have hdescent : baseEnd_3812596 < baseStart_3812596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812601 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_3812601 : Nat := 118140960795 + 3812601 * 2 ^ 59
def prefixEnd_3812601 : Nat := 4983230072969 + 3 ^ 40 * 3812601 * 2
def baseEnd_3812601 : Nat := 652565618937514304917891

theorem tailTrace_3812601 : CollatzResearch.WordTrace tailWord_3812601 prefixEnd_3812601 652565618937514304917891 := by
  unfold tailWord_3812601
  simp only [CollatzResearch.WordTrace]
  refine ⟨139056982460605192255973657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92704654973736794837315771 139056982460605192255973657)
  ·
    refine ⟨104292736845453894191980243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139056982460605192255973657 104292736845453894191980243)
    ·
      refine ⟨156439105268180841287970365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104292736845453894191980243 156439105268180841287970365)
      ·
        refine ⟨58664664475567815482988887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156439105268180841287970365 58664664475567815482988887)
        ·
          refine ⟨87996996713351723224483331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58664664475567815482988887 87996996713351723224483331)
          ·
            refine ⟨131995495070027584836724997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87996996713351723224483331 131995495070027584836724997)
            ·
              refine ⟨24749155325630172156885937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131995495070027584836724997 24749155325630172156885937)
              ·
                refine ⟨18561866494222629117664453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24749155325630172156885937 18561866494222629117664453)
                ·
                  refine ⟨3480349967666742959562085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18561866494222629117664453 3480349967666742959562085)
                  ·
                    refine ⟨652565618937514304917891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480349967666742959562085 652565618937514304917891)
                    ·
                      rfl

theorem cell23_3812601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_3812601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812601 prefixEnd_3812601 := by exact prefixLift 3812601
  have htrace : WordTrace (prefixWord ++ tailWord_3812601) baseStart_3812601 baseEnd_3812601 := by
    simpa [prefixWord, tailWord_3812601, baseEnd_3812601] using wordTrace_append hprefix tailTrace_3812601
  have hstable : (prefixWord ++ tailWord_3812601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812601).length < 2 ^ (prefixWord ++ tailWord_3812601).sum := by decide
  have hdescent : baseEnd_3812601 < baseStart_3812601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812608 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2]
def baseStart_3812608 : Nat := 118140960795 + 3812608 * 2 ^ 59
def prefixEnd_3812608 : Nat := 4983230072969 + 3 ^ 40 * 3812608 * 2
def baseEnd_3812608 : Nat := 1957700451177124387366141

theorem tailTrace_3812608 : CollatzResearch.WordTrace tailWord_3812608 prefixEnd_3812608 1957700451177124387366141 := by
  unfold tailWord_3812608
  simp only [CollatzResearch.WordTrace]
  refine ⟨69528618885789916225739239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92704825181053221634318985 69528618885789916225739239)
  ·
    refine ⟨104292928328684874338608859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69528618885789916225739239 104292928328684874338608859)
    ·
      refine ⟨156439392493027311507913289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104292928328684874338608859 156439392493027311507913289)
      ·
        refine ⟨117329544369770483630934967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156439392493027311507913289 117329544369770483630934967)
        ·
          refine ⟨175994316554655725446402451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117329544369770483630934967 175994316554655725446402451)
          ·
            refine ⟨263991474831983588169603677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175994316554655725446402451 263991474831983588169603677)
            ·
              refine ⟨98996803061993845563601379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263991474831983588169603677 98996803061993845563601379)
              ·
                refine ⟨148495204592990768345402069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98996803061993845563601379 148495204592990768345402069)
                ·
                  refine ⟨3480356357648221133095361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148495204592990768345402069 3480356357648221133095361)
                  ·
                    refine ⟨2610267268236165849821521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480356357648221133095361 2610267268236165849821521)
                    ·
                      refine ⟨1957700451177124387366141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610267268236165849821521 1957700451177124387366141)
                      ·
                        rfl

theorem cell23_3812608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_3812608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812608 prefixEnd_3812608 := by exact prefixLift 3812608
  have htrace : WordTrace (prefixWord ++ tailWord_3812608) baseStart_3812608 baseEnd_3812608 := by
    simpa [prefixWord, tailWord_3812608, baseEnd_3812608] using wordTrace_append hprefix tailTrace_3812608
  have hstable : (prefixWord ++ tailWord_3812608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812608).length < 2 ^ (prefixWord ++ tailWord_3812608).sum := by decide
  have hdescent : baseEnd_3812608 < baseStart_3812608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812625 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_3812625 : Nat := 118140960795 + 3812625 * 2 ^ 59
def prefixEnd_3812625 : Nat := 4983230072969 + 3 ^ 40 * 3812625 * 2
def baseEnd_3812625 : Nat := 1957709180348250820853563

theorem tailTrace_3812625 : CollatzResearch.WordTrace tailWord_3812625 prefixEnd_3812625 1957709180348250820853563 := by
  unfold tailWord_3812625
  simp only [CollatzResearch.WordTrace]
  refine ⟨139057857812518244354847329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92705238541678829569898219 139057857812518244354847329)
  ·
    refine ⟨104293393359388683266135497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139057857812518244354847329 104293393359388683266135497)
    ·
      refine ⟨78220045019541512449601623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104293393359388683266135497 78220045019541512449601623)
      ·
        refine ⟨117330067529312268674402435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78220045019541512449601623 117330067529312268674402435)
        ·
          refine ⟨175995101293968403011603653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117330067529312268674402435 175995101293968403011603653)
          ·
            refine ⟨32999081492619075564675685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175995101293968403011603653 32999081492619075564675685)
            ·
              refine ⟨6187327779866076668376691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32999081492619075564675685 6187327779866076668376691)
              ·
                refine ⟨9280991669799115002565037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187327779866076668376691 9280991669799115002565037)
                ·
                  refine ⟨3480371876174668125961889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9280991669799115002565037 3480371876174668125961889)
                  ·
                    refine ⟨2610278907131001094471417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480371876174668125961889 2610278907131001094471417)
                    ·
                      refine ⟨1957709180348250820853563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610278907131001094471417 1957709180348250820853563)
                      ·
                        rfl

theorem cell23_3812625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_3812625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812625 prefixEnd_3812625 := by exact prefixLift 3812625
  have htrace : WordTrace (prefixWord ++ tailWord_3812625) baseStart_3812625 baseEnd_3812625 := by
    simpa [prefixWord, tailWord_3812625, baseEnd_3812625] using wordTrace_append hprefix tailTrace_3812625
  have hstable : (prefixWord ++ tailWord_3812625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812625).length < 2 ^ (prefixWord ++ tailWord_3812625).sum := by decide
  have hdescent : baseEnd_3812625 < baseStart_3812625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812645 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_3812645 : Nat := 118140960795 + 3812645 * 2 ^ 59
def prefixEnd_3812645 : Nat := 4983230072969 + 3 ^ 40 * 3812645 * 2
def baseEnd_3812645 : Nat := 1957719449961340742603471

theorem tailTrace_3812645 : CollatzResearch.WordTrace tailWord_3812645 prefixEnd_3812645 1957719449961340742603471 := by
  unfold tailWord_3812645
  simp only [CollatzResearch.WordTrace]
  refine ⟨139058587272445787770575389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92705724848297191847050259 139058587272445787770575389)
  ·
    refine ⟨52146970227167170413965771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139058587272445787770575389 52146970227167170413965771)
    ·
      refine ⟨78220455340750755620948657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52146970227167170413965771 78220455340750755620948657)
      ·
        refine ⟨58665341505563066715711493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78220455340750755620948657 58665341505563066715711493)
        ·
          refine ⟨10999751532293075009195905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58665341505563066715711493 10999751532293075009195905)
          ·
            refine ⟨8249813649219806256896929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10999751532293075009195905 8249813649219806256896929)
            ·
              refine ⟨6187360236914854692672697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249813649219806256896929 6187360236914854692672697)
              ·
                refine ⟨4640520177686141019504523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187360236914854692672697 4640520177686141019504523)
                ·
                  refine ⟨6960780266529211529256785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640520177686141019504523 6960780266529211529256785)
                  ·
                    refine ⟨5220585199896908646942589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6960780266529211529256785 5220585199896908646942589)
                    ·
                      refine ⟨1957719449961340742603471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220585199896908646942589 1957719449961340742603471)
                      ·
                        rfl

theorem cell23_3812645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_3812645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812645 prefixEnd_3812645 := by exact prefixLift 3812645
  have htrace : WordTrace (prefixWord ++ tailWord_3812645) baseStart_3812645 baseEnd_3812645 := by
    simpa [prefixWord, tailWord_3812645, baseEnd_3812645] using wordTrace_append hprefix tailTrace_3812645
  have hstable : (prefixWord ++ tailWord_3812645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812645).length < 2 ^ (prefixWord ++ tailWord_3812645).sum := by decide
  have hdescent : baseEnd_3812645 < baseStart_3812645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812648 : List Nat := [2, 1, 5, 1, 2, 1, 4, 7]
def baseStart_3812648 : Nat := 118140960795 + 3812648 * 2 ^ 59
def prefixEnd_3812648 : Nat := 4983230072969 + 3 ^ 40 * 3812648 * 2
def baseEnd_3812648 : Nat := 72508184829752008550591

theorem tailTrace_3812648 : CollatzResearch.WordTrace tailWord_3812648 prefixEnd_3812648 72508184829752008550591 := by
  unfold tailWord_3812648
  simp only [CollatzResearch.WordTrace]
  refine ⟨69529348345717459641467299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92705797794289946188623065 69529348345717459641467299)
  ·
    refine ⟨104294022518576189462200949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69529348345717459641467299 104294022518576189462200949)
    ·
      refine ⟨9777564611116517762081339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104294022518576189462200949 9777564611116517762081339)
      ·
        refine ⟨14666346916674776643122009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9777564611116517762081339 14666346916674776643122009)
        ·
          refine ⟨10999760187506082482341507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666346916674776643122009 10999760187506082482341507)
          ·
            refine ⟨16499640281259123723512261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10999760187506082482341507 16499640281259123723512261)
            ·
              refine ⟨3093682552736085698158549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16499640281259123723512261 3093682552736085698158549)
              ·
                refine ⟨72508184829752008550591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3093682552736085698158549 72508184829752008550591)
                ·
                  rfl

theorem cell23_3812648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 7].length) (baseStart_3812648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812648 prefixEnd_3812648 := by exact prefixLift 3812648
  have htrace : WordTrace (prefixWord ++ tailWord_3812648) baseStart_3812648 baseEnd_3812648 := by
    simpa [prefixWord, tailWord_3812648, baseEnd_3812648] using wordTrace_append hprefix tailTrace_3812648
  have hstable : (prefixWord ++ tailWord_3812648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812648).length < 2 ^ (prefixWord ++ tailWord_3812648).sum := by decide
  have hdescent : baseEnd_3812648 < baseStart_3812648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812659 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 1, 2, 2]
def baseStart_3812659 : Nat := 118140960795 + 3812659 * 2 ^ 59
def prefixEnd_3812659 : Nat := 4983230072969 + 3 ^ 40 * 3812659 * 2
def baseEnd_3812659 : Nat := 1957726638690503687828407

theorem tailTrace_3812659 : CollatzResearch.WordTrace tailWord_3812659 prefixEnd_3812659 1957726638690503687828407 := by
  unfold tailWord_3812659
  simp only [CollatzResearch.WordTrace]
  refine ⟨139059097894395068161585031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92706065262930045441056687 139059097894395068161585031)
  ·
    refine ⟨208588646841592602242377547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139059097894395068161585031 208588646841592602242377547)
    ·
      refine ⟨312882970262388903363566321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208588646841592602242377547 312882970262388903363566321)
      ·
        refine ⟨234662227696791677522674741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312882970262388903363566321 234662227696791677522674741)
        ·
          refine ⟨21999583846574219767750757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234662227696791677522674741 21999583846574219767750757)
          ·
            refine ⟨4124921971232666206453267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21999583846574219767750757 4124921971232666206453267)
            ·
              refine ⟨6187382956848999309679901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124921971232666206453267 6187382956848999309679901)
              ·
                refine ⟨2320268608818374741129963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6187382956848999309679901 2320268608818374741129963)
                ·
                  refine ⟨3480402913227562111694945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320268608818374741129963 3480402913227562111694945)
                  ·
                    refine ⟨2610302184920671583771209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480402913227562111694945 2610302184920671583771209)
                    ·
                      refine ⟨1957726638690503687828407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610302184920671583771209 1957726638690503687828407)
                      ·
                        rfl

theorem cell23_3812659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 2, 2].length) (baseStart_3812659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812659 prefixEnd_3812659 := by exact prefixLift 3812659
  have htrace : WordTrace (prefixWord ++ tailWord_3812659) baseStart_3812659 baseEnd_3812659 := by
    simpa [prefixWord, tailWord_3812659, baseEnd_3812659] using wordTrace_append hprefix tailTrace_3812659
  have hstable : (prefixWord ++ tailWord_3812659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812659).length < 2 ^ (prefixWord ++ tailWord_3812659).sum := by decide
  have hdescent : baseEnd_3812659 < baseStart_3812659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812662 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3812662 : Nat := 118140960795 + 3812662 * 2 ^ 59
def prefixEnd_3812662 : Nat := 4983230072969 + 3 ^ 40 * 3812662 * 2
def baseEnd_3812662 : Nat := 1957728179132467176090893

theorem tailTrace_3812662 : CollatzResearch.WordTrace tailWord_3812662 prefixEnd_3812662 1957728179132467176090893 := by
  unfold tailWord_3812662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691200457086512479621515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92706138208922799782629493 8691200457086512479621515)
  ·
    refine ⟨13036800685629768719432273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8691200457086512479621515 13036800685629768719432273)
    ·
      refine ⟨9777600514222326539574205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13036800685629768719432273 9777600514222326539574205)
      ·
        refine ⟨3666600192833372452340327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9777600514222326539574205 3666600192833372452340327)
        ·
          refine ⟨5499900289250058678510491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666600192833372452340327 5499900289250058678510491)
          ·
            refine ⟨8249850433875088017765737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499900289250058678510491 8249850433875088017765737)
            ·
              refine ⟨6187387825406316013324303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249850433875088017765737 6187387825406316013324303)
              ·
                refine ⟨9281081738109474019986455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6187387825406316013324303 9281081738109474019986455)
                ·
                  refine ⟨13921622607164211029979683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281081738109474019986455 13921622607164211029979683)
                  ·
                    refine ⟨20882433910746316544969525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13921622607164211029979683 20882433910746316544969525)
                    ·
                      refine ⟨1957728179132467176090893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20882433910746316544969525 1957728179132467176090893)
                      ·
                        rfl

theorem cell23_3812662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3812662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812662 prefixEnd_3812662 := by exact prefixLift 3812662
  have htrace : WordTrace (prefixWord ++ tailWord_3812662) baseStart_3812662 baseEnd_3812662 := by
    simpa [prefixWord, tailWord_3812662, baseEnd_3812662] using wordTrace_append hprefix tailTrace_3812662
  have hstable : (prefixWord ++ tailWord_3812662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812662).length < 2 ^ (prefixWord ++ tailWord_3812662).sum := by decide
  have hdescent : baseEnd_3812662 < baseStart_3812662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812732 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_3812732 : Nat := 118140960795 + 3812732 * 2 ^ 59
def prefixEnd_3812732 : Nat := 4983230072969 + 3 ^ 40 * 3812732 * 2
def baseEnd_3812732 : Nat := 1957764122778281902215571

theorem tailTrace_3812732 : CollatzResearch.WordTrace tailWord_3812732 prefixEnd_3812732 1957764122778281902215571 := by
  unfold tailWord_3812732
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530880211565300814496225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92707840282087067752661633 69530880211565300814496225)
  ·
    refine ⟨52148160158673975610872169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69530880211565300814496225 52148160158673975610872169)
    ·
      refine ⟨39111120119005481708154127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52148160158673975610872169 39111120119005481708154127)
      ·
        refine ⟨58666680178508222562231191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39111120119005481708154127 58666680178508222562231191)
        ·
          refine ⟨88000020267762333843346787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58666680178508222562231191 88000020267762333843346787)
          ·
            refine ⟨132000030401643500765020181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88000020267762333843346787 132000030401643500765020181)
            ·
              refine ⟨6187501425077039098360321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132000030401643500765020181 6187501425077039098360321)
              ·
                refine ⟨4640626068807779323770241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187501425077039098360321 4640626068807779323770241)
                ·
                  refine ⟨3480469551605834492827681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640626068807779323770241 3480469551605834492827681)
                  ·
                    refine ⟨2610352163704375869620761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480469551605834492827681 2610352163704375869620761)
                    ·
                      refine ⟨1957764122778281902215571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610352163704375869620761 1957764122778281902215571)
                      ·
                        rfl

theorem cell23_3812732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_3812732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812732 prefixEnd_3812732 := by exact prefixLift 3812732
  have htrace : WordTrace (prefixWord ++ tailWord_3812732) baseStart_3812732 baseEnd_3812732 := by
    simpa [prefixWord, tailWord_3812732, baseEnd_3812732] using wordTrace_append hprefix tailTrace_3812732
  have hstable : (prefixWord ++ tailWord_3812732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812732).length < 2 ^ (prefixWord ++ tailWord_3812732).sum := by decide
  have hdescent : baseEnd_3812732 < baseStart_3812732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812748 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_3812748 : Nat := 118140960795 + 3812748 * 2 ^ 59
def prefixEnd_3812748 : Nat := 4983230072969 + 3 ^ 40 * 3812748 * 2
def baseEnd_3812748 : Nat := 1957772338468753839615497

theorem tailTrace_3812748 : CollatzResearch.WordTrace tailWord_3812748 prefixEnd_3812748 1957772338468753839615497 := by
  unfold tailWord_3812748
  simp only [CollatzResearch.WordTrace]
  refine ⟨69531171995536318180787449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92708229327381757574383265 69531171995536318180787449)
  ·
    refine ⟨52148378996652238635590587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69531171995536318180787449 52148378996652238635590587)
    ·
      refine ⟨78222568494978357953385881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52148378996652238635590587 78222568494978357953385881)
      ·
        refine ⟨58666926371233768465039411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78222568494978357953385881 58666926371233768465039411)
        ·
          refine ⟨88000389556850652697559117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58666926371233768465039411 88000389556850652697559117)
          ·
            refine ⟨33000146083818994761584669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88000389556850652697559117 33000146083818994761584669)
            ·
              refine ⟨12375054781432123035594251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33000146083818994761584669 12375054781432123035594251)
              ·
                refine ⟨18562582172148184553391377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375054781432123035594251 18562582172148184553391377)
                ·
                  refine ⟨13921936629111138415043533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18562582172148184553391377 13921936629111138415043533)
                  ·
                    refine ⟨5220726235916676905641325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13921936629111138415043533 5220726235916676905641325)
                    ·
                      refine ⟨1957772338468753839615497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220726235916676905641325 1957772338468753839615497)
                      ·
                        rfl

theorem cell23_3812748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_3812748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812748 prefixEnd_3812748 := by exact prefixLift 3812748
  have htrace : WordTrace (prefixWord ++ tailWord_3812748) baseStart_3812748 baseEnd_3812748 := by
    simpa [prefixWord, tailWord_3812748, baseEnd_3812748] using wordTrace_append hprefix tailTrace_3812748
  have hstable : (prefixWord ++ tailWord_3812748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812748).length < 2 ^ (prefixWord ++ tailWord_3812748).sum := by decide
  have hdescent : baseEnd_3812748 < baseStart_3812748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812808 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_3812808 : Nat := 118140960795 + 3812808 * 2 ^ 59
def prefixEnd_3812808 : Nat := 4983230072969 + 3 ^ 40 * 3812808 * 2
def baseEnd_3812808 : Nat := 1957803147308023604865221

theorem tailTrace_3812808 : CollatzResearch.WordTrace tailWord_3812808 prefixEnd_3812808 1957803147308023604865221 := by
  unfold tailWord_3812808
  simp only [CollatzResearch.WordTrace]
  refine ⟨69532266185427633304379539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92709688247236844405839385 69532266185427633304379539)
  ·
    refine ⟨104298399278141449956569309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69532266185427633304379539 104298399278141449956569309)
    ·
      refine ⟨39111899729303043733713491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104298399278141449956569309 39111899729303043733713491)
      ·
        refine ⟨58667849593954565600570237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39111899729303043733713491 58667849593954565600570237)
        ·
          refine ⟨22000443597732962100213839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58667849593954565600570237 22000443597732962100213839)
          ·
            refine ⟨33000665396599443150320759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000443597732962100213839 33000665396599443150320759)
            ·
              refine ⟨49500998094899164725481139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33000665396599443150320759 49500998094899164725481139)
              ·
                refine ⟨74251497142348747088221709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49500998094899164725481139 74251497142348747088221709)
                ·
                  refine ⟨27844311428380780158083141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74251497142348747088221709 27844311428380780158083141)
                  ·
                    refine ⟨5220808392821396279640589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27844311428380780158083141 5220808392821396279640589)
                    ·
                      refine ⟨1957803147308023604865221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220808392821396279640589 1957803147308023604865221)
                      ·
                        rfl

theorem cell23_3812808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_3812808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812808 prefixEnd_3812808 := by exact prefixLift 3812808
  have htrace : WordTrace (prefixWord ++ tailWord_3812808) baseStart_3812808 baseEnd_3812808 := by
    simpa [prefixWord, tailWord_3812808, baseEnd_3812808] using wordTrace_append hprefix tailTrace_3812808
  have hstable : (prefixWord ++ tailWord_3812808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812808).length < 2 ^ (prefixWord ++ tailWord_3812808).sum := by decide
  have hdescent : baseEnd_3812808 < baseStart_3812808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812841 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_3812841 : Nat := 118140960795 + 3812841 * 2 ^ 59
def prefixEnd_3812841 : Nat := 4983230072969 + 3 ^ 40 * 3812841 * 2
def baseEnd_3812841 : Nat := 652606697389873991917523

theorem tailTrace_3812841 : CollatzResearch.WordTrace tailWord_3812841 prefixEnd_3812841 652606697389873991917523 := by
  unfold tailWord_3812841
  simp only [CollatzResearch.WordTrace]
  refine ⟨139065735979735713244710377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92710490653157142163140251 139065735979735713244710377)
  ·
    refine ⟨104299301984801784933532783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139065735979735713244710377 104299301984801784933532783)
    ·
      refine ⟨156448952977202677400299175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104299301984801784933532783 156448952977202677400299175)
      ·
        refine ⟨234673429465804016100448763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156448952977202677400299175 234673429465804016100448763)
        ·
          refine ⟨352010144198706024150673145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234673429465804016100448763 352010144198706024150673145)
          ·
            refine ⟨264007608149029518113004859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352010144198706024150673145 264007608149029518113004859)
            ·
              refine ⟨396011412223544277169507289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264007608149029518113004859 396011412223544277169507289)
              ·
                refine ⟨297008559167658207877130467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396011412223544277169507289 297008559167658207877130467)
                ·
                  refine ⟨445512838751487311815695701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297008559167658207877130467 445512838751487311815695701)
                  ·
                    refine ⟨652606697389873991917523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 445512838751487311815695701 652606697389873991917523)
                    ·
                      rfl

theorem cell23_3812841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_3812841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812841 prefixEnd_3812841 := by exact prefixLift 3812841
  have htrace : WordTrace (prefixWord ++ tailWord_3812841) baseStart_3812841 baseEnd_3812841 := by
    simpa [prefixWord, tailWord_3812841, baseEnd_3812841] using wordTrace_append hprefix tailTrace_3812841
  have hstable : (prefixWord ++ tailWord_3812841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812841).length < 2 ^ (prefixWord ++ tailWord_3812841).sum := by decide
  have hdescent : baseEnd_3812841 < baseStart_3812841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812842 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_3812842 : Nat := 118140960795 + 3812842 * 2 ^ 59
def prefixEnd_3812842 : Nat := 4983230072969 + 3 ^ 40 * 3812842 * 2
def baseEnd_3812842 : Nat := 1957820605650276471840065

theorem tailTrace_3812842 : CollatzResearch.WordTrace tailWord_3812842 prefixEnd_3812842 1957820605650276471840065 := by
  unfold tailWord_3812842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34766443113183022603874195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92710514968488060276997853 34766443113183022603874195)
  ·
    refine ⟨52149664669774533905811293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34766443113183022603874195 52149664669774533905811293)
    ·
      refine ⟨19556124251165450214679235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52149664669774533905811293 19556124251165450214679235)
      ·
        refine ⟨29334186376748175322018853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556124251165450214679235 29334186376748175322018853)
        ·
          refine ⟨5500159945640282872878535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29334186376748175322018853 5500159945640282872878535)
          ·
            refine ⟨8250239918460424309317803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500159945640282872878535 8250239918460424309317803)
            ·
              refine ⟨12375359877690636463976705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250239918460424309317803 12375359877690636463976705)
              ·
                refine ⟨9281519908267977347982529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375359877690636463976705 9281519908267977347982529)
                ·
                  refine ⟨6961139931200983010986897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9281519908267977347982529 6961139931200983010986897)
                  ·
                    refine ⟨5220854948400737258240173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961139931200983010986897 5220854948400737258240173)
                    ·
                      refine ⟨1957820605650276471840065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220854948400737258240173 1957820605650276471840065)
                      ·
                        rfl

theorem cell23_3812842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_3812842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812842 prefixEnd_3812842 := by exact prefixLift 3812842
  have htrace : WordTrace (prefixWord ++ tailWord_3812842) baseStart_3812842 baseEnd_3812842 := by
    simpa [prefixWord, tailWord_3812842, baseEnd_3812842] using wordTrace_append hprefix tailTrace_3812842
  have hstable : (prefixWord ++ tailWord_3812842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812842).length < 2 ^ (prefixWord ++ tailWord_3812842).sum := by decide
  have hdescent : baseEnd_3812842 < baseStart_3812842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812849 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 1, 4]
def baseStart_3812849 : Nat := 118140960795 + 3812849 * 2 ^ 59
def prefixEnd_3812849 : Nat := 4983230072969 + 3 ^ 40 * 3812849 * 2
def baseEnd_3812849 : Nat := 652608066671619314817511

theorem tailTrace_3812849 : CollatzResearch.WordTrace tailWord_3812849 prefixEnd_3812849 652608066671619314817511 := by
  unfold tailWord_3812849
  simp only [CollatzResearch.WordTrace]
  refine ⟨139066027763706730611001601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92710685175804487074001067 139066027763706730611001601)
  ·
    refine ⟨104299520822780047958251201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139066027763706730611001601 104299520822780047958251201)
    ·
      refine ⟨78224640617085035968688401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104299520822780047958251201 78224640617085035968688401)
      ·
        refine ⟨58668480462813776976516301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78224640617085035968688401 58668480462813776976516301)
        ·
          refine ⟨22000680173555166366193613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58668480462813776976516301 22000680173555166366193613)
          ·
            refine ⟨8250255065083187387322605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22000680173555166366193613 8250255065083187387322605)
            ·
              refine ⟨3093845649406195270245977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8250255065083187387322605 3093845649406195270245977)
              ·
                refine ⟨2320384237054646452684483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093845649406195270245977 2320384237054646452684483)
                ·
                  refine ⟨3480576355581969679026725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320384237054646452684483 3480576355581969679026725)
                  ·
                    refine ⟨652608066671619314817511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480576355581969679026725 652608066671619314817511)
                    ·
                      rfl

theorem cell23_3812849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_3812849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812849 prefixEnd_3812849 := by exact prefixLift 3812849
  have htrace : WordTrace (prefixWord ++ tailWord_3812849) baseStart_3812849 baseEnd_3812849 := by
    simpa [prefixWord, tailWord_3812849, baseEnd_3812849] using wordTrace_append hprefix tailTrace_3812849
  have hstable : (prefixWord ++ tailWord_3812849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812849).length < 2 ^ (prefixWord ++ tailWord_3812849).sum := by decide
  have hdescent : baseEnd_3812849 < baseStart_3812849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812855 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_3812855 : Nat := 118140960795 + 3812855 * 2 ^ 59
def prefixEnd_3812855 : Nat := 4983230072969 + 3 ^ 40 * 3812855 * 2
def baseEnd_3812855 : Nat := 1957827280898784920977505

theorem tailTrace_3812855 : CollatzResearch.WordTrace tailWord_3812855 prefixEnd_3812855 1957827280898784920977505 := by
  unfold tailWord_3812855
  simp only [CollatzResearch.WordTrace]
  refine ⟨139066246601684993635720019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92710831067789995757146679 139066246601684993635720019)
  ·
    refine ⟨208599369902527490453580029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139066246601684993635720019 208599369902527490453580029)
    ·
      refine ⟨78224763713447808920092511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208599369902527490453580029 78224763713447808920092511)
      ·
        refine ⟨117337145570171713380138767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78224763713447808920092511 117337145570171713380138767)
        ·
          refine ⟨176005718355257570070208151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117337145570171713380138767 176005718355257570070208151)
          ·
            refine ⟨264008577532886355105312227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176005718355257570070208151 264008577532886355105312227)
            ·
              refine ⟨396012866299329532657968341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264008577532886355105312227 396012866299329532657968341)
              ·
                refine ⟨9281551553890535921671133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396012866299329532657968341 9281551553890535921671133)
                ·
                  refine ⟨3480581832708950970626675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281551553890535921671133 3480581832708950970626675)
                  ·
                    refine ⟨5220872749063426455940013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480581832708950970626675 5220872749063426455940013)
                    ·
                      refine ⟨1957827280898784920977505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220872749063426455940013 1957827280898784920977505)
                      ·
                        rfl

theorem cell23_3812855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_3812855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812855 prefixEnd_3812855 := by exact prefixLift 3812855
  have htrace : WordTrace (prefixWord ++ tailWord_3812855) baseStart_3812855 baseEnd_3812855 := by
    simpa [prefixWord, tailWord_3812855, baseEnd_3812855] using wordTrace_append hprefix tailTrace_3812855
  have hstable : (prefixWord ++ tailWord_3812855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812855).length < 2 ^ (prefixWord ++ tailWord_3812855).sum := by decide
  have hdescent : baseEnd_3812855 < baseStart_3812855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812858 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_3812858 : Nat := 118140960795 + 3812858 * 2 ^ 59
def prefixEnd_3812858 : Nat := 4983230072969 + 3 ^ 40 * 3812858 * 2
def baseEnd_3812858 : Nat := 652609607113582803079997

theorem tailTrace_3812858 : CollatzResearch.WordTrace tailWord_3812858 prefixEnd_3812858 652609607113582803079997 := by
  unfold tailWord_3812858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34766589005168531287019807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92710904013782750098719485 34766589005168531287019807)
  ·
    refine ⟨52149883507752796930529711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34766589005168531287019807 52149883507752796930529711)
    ·
      refine ⟨78224825261629195395794567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52149883507752796930529711 78224825261629195395794567)
      ·
        refine ⟨117337237892443793093691851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78224825261629195395794567 117337237892443793093691851)
        ·
          refine ⟨176005856838665689640537777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117337237892443793093691851 176005856838665689640537777)
          ·
            refine ⟨132004392628999267230403333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176005856838665689640537777 132004392628999267230403333)
            ·
              refine ⟨24750823617937362605700625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132004392628999267230403333 24750823617937362605700625)
              ·
                refine ⟨18563117713453021954275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24750823617937362605700625 18563117713453021954275469)
                ·
                  refine ⟨6961169142544883232853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18563117713453021954275469 6961169142544883232853301)
                  ·
                    refine ⟨652609607113582803079997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6961169142544883232853301 652609607113582803079997)
                    ·
                      rfl

theorem cell23_3812858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_3812858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812858 prefixEnd_3812858 := by exact prefixLift 3812858
  have htrace : WordTrace (prefixWord ++ tailWord_3812858) baseStart_3812858 baseEnd_3812858 := by
    simpa [prefixWord, tailWord_3812858, baseEnd_3812858] using wordTrace_append hprefix tailTrace_3812858
  have hstable : (prefixWord ++ tailWord_3812858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812858).length < 2 ^ (prefixWord ++ tailWord_3812858).sum := by decide
  have hdescent : baseEnd_3812858 < baseStart_3812858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812875 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 3, 5]
def baseStart_3812875 : Nat := 118140960795 + 3812875 * 2 ^ 59
def prefixEnd_3812875 : Nat := 4983230072969 + 3 ^ 40 * 3812875 * 2
def baseEnd_3812875 : Nat := 652612516837291614242471

theorem tailTrace_3812875 : CollatzResearch.WordTrace tailWord_3812875 prefixEnd_3812875 652612516837291614242471 := by
  unfold tailWord_3812875
  simp only [CollatzResearch.WordTrace]
  refine ⟨139066976061612537051448079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92711317374408358034298719 139066976061612537051448079)
  ·
    refine ⟨208600464092418805577172119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139066976061612537051448079 208600464092418805577172119)
    ·
      refine ⟨312900696138628208365758179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208600464092418805577172119 312900696138628208365758179)
      ·
        refine ⟨469351044207942312548637269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312900696138628208365758179 469351044207942312548637269)
        ·
          refine ⟨5500207549311823975179343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 469351044207942312548637269 5500207549311823975179343)
          ·
            refine ⟨8250311323967735962769015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500207549311823975179343 8250311323967735962769015)
            ·
              refine ⟨12375466985951603944153523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250311323967735962769015 12375466985951603944153523)
              ·
                refine ⟨18563200478927405916230285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375466985951603944153523 18563200478927405916230285)
                ·
                  refine ⟨6961200179597777218586357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18563200478927405916230285 6961200179597777218586357)
                  ·
                    refine ⟨652612516837291614242471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6961200179597777218586357 652612516837291614242471)
                    ·
                      rfl

theorem cell23_3812875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 5].length) (baseStart_3812875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812875 prefixEnd_3812875 := by exact prefixLift 3812875
  have htrace : WordTrace (prefixWord ++ tailWord_3812875) baseStart_3812875 baseEnd_3812875 := by
    simpa [prefixWord, tailWord_3812875, baseEnd_3812875] using wordTrace_append hprefix tailTrace_3812875
  have hstable : (prefixWord ++ tailWord_3812875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812875).length < 2 ^ (prefixWord ++ tailWord_3812875).sum := by decide
  have hdescent : baseEnd_3812875 < baseStart_3812875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812892 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_3812892 : Nat := 118140960795 + 3812892 * 2 ^ 59
def prefixEnd_3812892 : Nat := 4983230072969 + 3 ^ 40 * 3812892 * 2
def baseEnd_3812892 : Nat := 652615426561000425404945

theorem tailTrace_3812892 : CollatzResearch.WordTrace tailWord_3812892 prefixEnd_3812892 652615426561000425404945 := by
  unfold tailWord_3812892
  simp only [CollatzResearch.WordTrace]
  refine ⟨69533798051275474477408465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92711730735033965969877953 69533798051275474477408465)
  ·
    refine ⟨52150348538456605858056349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69533798051275474477408465 52150348538456605858056349)
    ·
      refine ⟨19556380701921227196771131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52150348538456605858056349 19556380701921227196771131)
      ·
        refine ⟨29334571052881840795156697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556380701921227196771131 29334571052881840795156697)
        ·
          refine ⟨22000928289661380596367523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29334571052881840795156697 22000928289661380596367523)
          ·
            refine ⟨33001392434492070894551285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000928289661380596367523 33001392434492070894551285)
            ·
              refine ⟨3093880540733631646364183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33001392434492070894551285 3093880540733631646364183)
              ·
                refine ⟨4640820811100447469546275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093880540733631646364183 4640820811100447469546275)
                ·
                  refine ⟨6961231216650671204319413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640820811100447469546275 6961231216650671204319413)
                  ·
                    refine ⟨652615426561000425404945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6961231216650671204319413 652615426561000425404945)
                    ·
                      rfl

theorem cell23_3812892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_3812892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812892 prefixEnd_3812892 := by exact prefixLift 3812892
  have htrace : WordTrace (prefixWord ++ tailWord_3812892) baseStart_3812892 baseEnd_3812892 := by
    simpa [prefixWord, tailWord_3812892, baseEnd_3812892] using wordTrace_append hprefix tailTrace_3812892
  have hstable : (prefixWord ++ tailWord_3812892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812892).length < 2 ^ (prefixWord ++ tailWord_3812892).sum := by decide
  have hdescent : baseEnd_3812892 < baseStart_3812892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812895 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 4]
def baseStart_3812895 : Nat := 118140960795 + 3812895 * 2 ^ 59
def prefixEnd_3812895 : Nat := 4983230072969 + 3 ^ 40 * 3812895 * 2
def baseEnd_3812895 : Nat := 1957847820124964764477321

theorem tailTrace_3812895 : CollatzResearch.WordTrace tailWord_3812895 prefixEnd_3812895 1957847820124964764477321 := by
  unfold tailWord_3812895
  simp only [CollatzResearch.WordTrace]
  refine ⟨139067705521540080467176139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92711803681026720311450759 139067705521540080467176139)
  ·
    refine ⟨208601558282310120700764209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139067705521540080467176139 208601558282310120700764209)
    ·
      refine ⟨156451168711732590525573157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208601558282310120700764209 156451168711732590525573157)
      ·
        refine ⟨29334594133449860723544967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156451168711732590525573157 29334594133449860723544967)
        ·
          refine ⟨44001891200174791085317451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29334594133449860723544967 44001891200174791085317451)
          ·
            refine ⟨66002836800262186627976177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44001891200174791085317451 66002836800262186627976177)
            ·
              refine ⟨49502127600196639970982133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66002836800262186627976177 49502127600196639970982133)
              ·
                refine ⟨4640824462518434997279575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49502127600196639970982133 4640824462518434997279575)
                ·
                  refine ⟨6961236693777652495919363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640824462518434997279575 6961236693777652495919363)
                  ·
                    refine ⟨10441855040666478743879045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961236693777652495919363 10441855040666478743879045)
                    ·
                      refine ⟨1957847820124964764477321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10441855040666478743879045 1957847820124964764477321)
                      ·
                        rfl

theorem cell23_3812895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_3812895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812895 prefixEnd_3812895 := by exact prefixLift 3812895
  have htrace : WordTrace (prefixWord ++ tailWord_3812895) baseStart_3812895 baseEnd_3812895 := by
    simpa [prefixWord, tailWord_3812895, baseEnd_3812895] using wordTrace_append hprefix tailTrace_3812895
  have hstable : (prefixWord ++ tailWord_3812895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812895).length < 2 ^ (prefixWord ++ tailWord_3812895).sum := by decide
  have hdescent : baseEnd_3812895 < baseStart_3812895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812912 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2]
def baseStart_3812912 : Nat := 118140960795 + 3812912 * 2 ^ 59
def prefixEnd_3812912 : Nat := 4983230072969 + 3 ^ 40 * 3812912 * 2
def baseEnd_3812912 : Nat := 1957856549296091197964743

theorem tailTrace_3812912 : CollatzResearch.WordTrace tailWord_3812912 prefixEnd_3812912 1957856549296091197964743 := by
  unfold tailWord_3812912
  simp only [CollatzResearch.WordTrace]
  refine ⟨69534162781239246185272495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92712217041652328247029993 69534162781239246185272495)
  ·
    refine ⟨104301244171858869277908743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69534162781239246185272495 104301244171858869277908743)
    ·
      refine ⟨156451866257788303916863115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104301244171858869277908743 156451866257788303916863115)
      ·
        refine ⟨234677799386682455875294673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156451866257788303916863115 234677799386682455875294673)
        ·
          refine ⟨176008349540011841906471005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234677799386682455875294673 176008349540011841906471005)
          ·
            refine ⟨66003131077504440714926627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176008349540011841906471005 66003131077504440714926627)
            ·
              refine ⟨99004696616256661072389941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66003131077504440714926627 99004696616256661072389941)
              ·
                refine ⟨9281690307774061975536557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99004696616256661072389941 9281690307774061975536557)
                ·
                  refine ⟨3480633865415273240826209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281690307774061975536557 3480633865415273240826209)
                  ·
                    refine ⟨2610475399061454930619657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480633865415273240826209 2610475399061454930619657)
                    ·
                      refine ⟨1957856549296091197964743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610475399061454930619657 1957856549296091197964743)
                      ·
                        rfl

theorem cell23_3812912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2].length) (baseStart_3812912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812912 prefixEnd_3812912 := by exact prefixLift 3812912
  have htrace : WordTrace (prefixWord ++ tailWord_3812912) baseStart_3812912 baseEnd_3812912 := by
    simpa [prefixWord, tailWord_3812912, baseEnd_3812912] using wordTrace_append hprefix tailTrace_3812912
  have hstable : (prefixWord ++ tailWord_3812912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812912).length < 2 ^ (prefixWord ++ tailWord_3812912).sum := by decide
  have hdescent : baseEnd_3812912 < baseStart_3812912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812915 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3]
def baseStart_3812915 : Nat := 118140960795 + 3812915 * 2 ^ 59
def prefixEnd_3812915 : Nat := 4983230072969 + 3 ^ 40 * 3812915 * 2
def baseEnd_3812915 : Nat := 1957858089738054686227229

theorem tailTrace_3812915 : CollatzResearch.WordTrace tailWord_3812915 prefixEnd_3812915 1957858089738054686227229 := by
  unfold tailWord_3812915
  simp only [CollatzResearch.WordTrace]
  refine ⟨139068434981467623882904199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92712289987645082588602799 139068434981467623882904199)
  ·
    refine ⟨208602652472201435824356299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139068434981467623882904199 208602652472201435824356299)
    ·
      refine ⟨312903978708302153736534449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208602652472201435824356299 312903978708302153736534449)
      ·
        refine ⟨234677984031226615302400837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312903978708302153736534449 234677984031226615302400837)
        ·
          refine ⟨44002122005854990369200157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234677984031226615302400837 44002122005854990369200157)
          ·
            refine ⟨16500795752195621388450059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44002122005854990369200157 16500795752195621388450059)
            ·
              refine ⟨24751193628293432082675089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500795752195621388450059 24751193628293432082675089)
              ·
                refine ⟨18563395221220074062006317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24751193628293432082675089 18563395221220074062006317)
                ·
                  refine ⟨6961273207957527773252369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18563395221220074062006317 6961273207957527773252369)
                  ·
                    refine ⟨5220954905968145829939277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961273207957527773252369 5220954905968145829939277)
                    ·
                      refine ⟨1957858089738054686227229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220954905968145829939277 1957858089738054686227229)
                      ·
                        rfl

theorem cell23_3812915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_3812915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812915 prefixEnd_3812915 := by exact prefixLift 3812915
  have htrace : WordTrace (prefixWord ++ tailWord_3812915) baseStart_3812915 baseEnd_3812915 := by
    simpa [prefixWord, tailWord_3812915, baseEnd_3812915] using wordTrace_append hprefix tailTrace_3812915
  have hstable : (prefixWord ++ tailWord_3812915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812915).length < 2 ^ (prefixWord ++ tailWord_3812915).sum := by decide
  have hdescent : baseEnd_3812915 < baseStart_3812915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812929 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3812929 : Nat := 118140960795 + 3812929 * 2 ^ 59
def prefixEnd_3812929 : Nat := 4983230072969 + 3 ^ 40 * 3812929 * 2
def baseEnd_3812929 : Nat := 1957865278467217631452165

theorem tailTrace_3812929 : CollatzResearch.WordTrace tailWord_3812929 prefixEnd_3812929 1957865278467217631452165 := by
  unfold tailWord_3812929
  simp only [CollatzResearch.WordTrace]
  refine ⟨139068945603416904273913841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92712630402277936182609227 139068945603416904273913841)
  ·
    refine ⟨104301709202562678205435381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139068945603416904273913841 104301709202562678205435381)
    ·
      refine ⟨9778285237740251081759567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104301709202562678205435381 9778285237740251081759567)
      ·
        refine ⟨14667427856610376622639351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778285237740251081759567 14667427856610376622639351)
        ·
          refine ⟨22001141784915564933959027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667427856610376622639351 22001141784915564933959027)
          ·
            refine ⟨33001712677373347400938541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22001141784915564933959027 33001712677373347400938541)
            ·
              refine ⟨12375642254015005275351953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33001712677373347400938541 12375642254015005275351953)
              ·
                refine ⟨9281731690511253956513965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375642254015005275351953 9281731690511253956513965)
                ·
                  refine ⟨3480649383941720233692737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281731690511253956513965 3480649383941720233692737)
                  ·
                    refine ⟨2610487037956290175269553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480649383941720233692737 2610487037956290175269553)
                    ·
                      refine ⟨1957865278467217631452165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610487037956290175269553 1957865278467217631452165)
                      ·
                        rfl

theorem cell23_3812929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3812929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812929 prefixEnd_3812929 := by exact prefixLift 3812929
  have htrace : WordTrace (prefixWord ++ tailWord_3812929) baseStart_3812929 baseEnd_3812929 := by
    simpa [prefixWord, tailWord_3812929, baseEnd_3812929] using wordTrace_append hprefix tailTrace_3812929
  have hstable : (prefixWord ++ tailWord_3812929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812929).length < 2 ^ (prefixWord ++ tailWord_3812929).sum := by decide
  have hdescent : baseEnd_3812929 < baseStart_3812929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812945 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_3812945 : Nat := 118140960795 + 3812945 * 2 ^ 59
def prefixEnd_3812945 : Nat := 4983230072969 + 3 ^ 40 * 3812945 * 2
def baseEnd_3812945 : Nat := 1957873494157689568852091

theorem tailTrace_3812945 : CollatzResearch.WordTrace tailWord_3812945 prefixEnd_3812945 1957873494157689568852091 := by
  unfold tailWord_3812945
  simp only [CollatzResearch.WordTrace]
  refine ⟨139069529171358939006496289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92713019447572626004330859 139069529171358939006496289)
  ·
    refine ⟨104302146878519204254872217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139069529171358939006496289 104302146878519204254872217)
    ·
      refine ⟨78226610158889403191154163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104302146878519204254872217 78226610158889403191154163)
      ·
        refine ⟨117339915238334104786731245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78226610158889403191154163 117339915238334104786731245)
        ·
          refine ⟨44002468214375289295024217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117339915238334104786731245 44002468214375289295024217)
          ·
            refine ⟨33001851160781466971268163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44002468214375289295024217 33001851160781466971268163)
            ·
              refine ⟨49502776741172200456902245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33001851160781466971268163 49502776741172200456902245)
              ·
                refine ⟨9281770638969787585669171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49502776741172200456902245 9281770638969787585669171)
                ·
                  refine ⟨13922655958454681378503757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9281770638969787585669171 13922655958454681378503757)
                  ·
                    refine ⟨5220995984420505516938909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13922655958454681378503757 5220995984420505516938909)
                    ·
                      refine ⟨1957873494157689568852091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5220995984420505516938909 1957873494157689568852091)
                      ·
                        rfl

theorem cell23_3812945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_3812945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812945 prefixEnd_3812945 := by exact prefixLift 3812945
  have htrace : WordTrace (prefixWord ++ tailWord_3812945) baseStart_3812945 baseEnd_3812945 := by
    simpa [prefixWord, tailWord_3812945, baseEnd_3812945] using wordTrace_append hprefix tailTrace_3812945
  have hstable : (prefixWord ++ tailWord_3812945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812945).length < 2 ^ (prefixWord ++ tailWord_3812945).sum := by decide
  have hdescent : baseEnd_3812945 < baseStart_3812945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812946 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_3812946 : Nat := 118140960795 + 3812946 * 2 ^ 59
def prefixEnd_3812946 : Nat := 4983230072969 + 3 ^ 40 * 3812946 * 2
def baseEnd_3812946 : Nat := 1957874007638344064939587

theorem tailTrace_3812946 : CollatzResearch.WordTrace tailWord_3812946 prefixEnd_3812946 1957874007638344064939587 := by
  unfold tailWord_3812946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767391411088829044320673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92713043762903544118188461 34767391411088829044320673)
  ·
    refine ⟨26075543558316621783240505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34767391411088829044320673 26075543558316621783240505)
    ·
      refine ⟨19556657668737466337430379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26075543558316621783240505 19556657668737466337430379)
      ·
        refine ⟨29334986503106199506145569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556657668737466337430379 29334986503106199506145569)
        ·
          refine ⟨22001239877329649629609177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29334986503106199506145569 22001239877329649629609177)
          ·
            refine ⟨16500929907997237222206883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22001239877329649629609177 16500929907997237222206883)
            ·
              refine ⟨24751394861995855833310325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500929907997237222206883 24751394861995855833310325)
              ·
                refine ⟨2320443268312111484372843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24751394861995855833310325 2320443268312111484372843)
                ·
                  refine ⟨3480664902468167226559265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320443268312111484372843 3480664902468167226559265)
                  ·
                    refine ⟨2610498676851125419919449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480664902468167226559265 2610498676851125419919449)
                    ·
                      refine ⟨1957874007638344064939587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610498676851125419919449 1957874007638344064939587)
                      ·
                        rfl

theorem cell23_3812946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_3812946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812946 prefixEnd_3812946 := by exact prefixLift 3812946
  have htrace : WordTrace (prefixWord ++ tailWord_3812946) baseStart_3812946 baseEnd_3812946 := by
    simpa [prefixWord, tailWord_3812946, baseEnd_3812946] using wordTrace_append hprefix tailTrace_3812946
  have hstable : (prefixWord ++ tailWord_3812946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812946).length < 2 ^ (prefixWord ++ tailWord_3812946).sum := by decide
  have hdescent : baseEnd_3812946 < baseStart_3812946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812989 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_3812989 : Nat := 118140960795 + 3812989 * 2 ^ 59
def prefixEnd_3812989 : Nat := 4983230072969 + 3 ^ 40 * 3812989 * 2
def baseEnd_3812989 : Nat := 1957896087306487396701889

theorem tailTrace_3812989 : CollatzResearch.WordTrace tailWord_3812989 prefixEnd_3812989 1957896087306487396701889 := by
  unfold tailWord_3812989
  simp only [CollatzResearch.WordTrace]
  refine ⟨139071133983199534521098021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92714089322133023014065347 139071133983199534521098021)
  ·
    refine ⟨26075837621849912722705879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139071133983199534521098021 26075837621849912722705879)
    ·
      refine ⟨39113756432774869084058819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26075837621849912722705879 39113756432774869084058819)
      ·
        refine ⟨58670634649162303626088229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39113756432774869084058819 58670634649162303626088229)
        ·
          refine ⟨11000743996717931929891543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58670634649162303626088229 11000743996717931929891543)
          ·
            refine ⟨16501115995076897894837315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000743996717931929891543 16501115995076897894837315)
            ·
              refine ⟨24751673992615346842255973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501115995076897894837315 24751673992615346842255973)
              ·
                refine ⟨4640938873615377532922995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24751673992615346842255973 4640938873615377532922995)
                ·
                  refine ⟨6961408310423066299384493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640938873615377532922995 6961408310423066299384493)
                  ·
                    refine ⟨2610528116408649862269185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6961408310423066299384493 2610528116408649862269185)
                    ·
                      refine ⟨1957896087306487396701889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610528116408649862269185 1957896087306487396701889)
                      ·
                        rfl

theorem cell23_3812989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_3812989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3812989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3812989 prefixEnd_3812989 := by exact prefixLift 3812989
  have htrace : WordTrace (prefixWord ++ tailWord_3812989) baseStart_3812989 baseEnd_3812989 := by
    simpa [prefixWord, tailWord_3812989, baseEnd_3812989] using wordTrace_append hprefix tailTrace_3812989
  have hstable : (prefixWord ++ tailWord_3812989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812989).length < 2 ^ (prefixWord ++ tailWord_3812989).sum := by decide
  have hdescent : baseEnd_3812989 < baseStart_3812989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813008 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 9]
def baseStart_3813008 : Nat := 118140960795 + 3813008 * 2 ^ 59
def prefixEnd_3813008 : Nat := 4983230072969 + 3 ^ 40 * 3813008 * 2
def baseEnd_3813008 : Nat := 217545093715435869151589

theorem tailTrace_3813008 : CollatzResearch.WordTrace tailWord_3813008 prefixEnd_3813008 217545093715435869151589 := by
  unfold tailWord_3813008
  simp only [CollatzResearch.WordTrace]
  refine ⟨69535913485065350383019839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92714551313420467177359785 69535913485065350383019839)
  ·
    refine ⟨104303870227598025574529759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69535913485065350383019839 104303870227598025574529759)
    ·
      refine ⟨156455805341397038361794639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104303870227598025574529759 156455805341397038361794639)
      ·
        refine ⟨234683708012095557542691959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156455805341397038361794639 234683708012095557542691959)
        ·
          refine ⟨352025562018143336314037939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234683708012095557542691959 352025562018143336314037939)
          ·
            refine ⟨528038343027215004471056909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352025562018143336314037939 528038343027215004471056909)
            ·
              refine ⟨198014378635205626676646341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528038343027215004471056909 198014378635205626676646341)
              ·
                refine ⟨37127695994101055001871189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198014378635205626676646341 37127695994101055001871189)
                ·
                  refine ⟨217545093715435869151589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37127695994101055001871189 217545093715435869151589)
                  ·
                    rfl

theorem cell23_3813008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_3813008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813008 prefixEnd_3813008 := by exact prefixLift 3813008
  have htrace : WordTrace (prefixWord ++ tailWord_3813008) baseStart_3813008 baseEnd_3813008 := by
    simpa [prefixWord, tailWord_3813008, baseEnd_3813008] using wordTrace_append hprefix tailTrace_3813008
  have hstable : (prefixWord ++ tailWord_3813008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813008).length < 2 ^ (prefixWord ++ tailWord_3813008).sum := by decide
  have hdescent : baseEnd_3813008 < baseStart_3813008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813075 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4]
def baseStart_3813075 : Nat := 118140960795 + 3813075 * 2 ^ 59
def prefixEnd_3813075 : Nat := 4983230072969 + 3 ^ 40 * 3813075 * 2
def baseEnd_3813075 : Nat := 1957940246642774060226493

theorem tailTrace_3813075 : CollatzResearch.WordTrace tailWord_3813075 prefixEnd_3813075 1957940246642774060226493 := by
  unfold tailWord_3813075
  simp only [CollatzResearch.WordTrace]
  refine ⟨139074270660887971208728679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92716180440591980805819119 139074270660887971208728679)
  ·
    refine ⟨208611405991331956813093019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139074270660887971208728679 208611405991331956813093019)
    ·
      refine ⟨312917108986997935219639529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208611405991331956813093019 312917108986997935219639529)
      ·
        refine ⟨234687831740248451414729647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312917108986997935219639529 234687831740248451414729647)
        ·
          refine ⟨352031747610372677122094471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234687831740248451414729647 352031747610372677122094471)
          ·
            refine ⟨528047621415559015683141707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352031747610372677122094471 528047621415559015683141707)
            ·
              refine ⟨792071432123338523524712561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528047621415559015683141707 792071432123338523524712561)
              ·
                refine ⟨594053574092503892643534421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792071432123338523524712561 594053574092503892643534421)
                ·
                  refine ⟨6961565321396529991916419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 594053574092503892643534421 6961565321396529991916419)
                  ·
                    refine ⟨10442347982094794987874629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961565321396529991916419 10442347982094794987874629)
                    ·
                      refine ⟨1957940246642774060226493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10442347982094794987874629 1957940246642774060226493)
                      ·
                        rfl

theorem cell23_3813075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_3813075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813075 prefixEnd_3813075 := by exact prefixLift 3813075
  have htrace : WordTrace (prefixWord ++ tailWord_3813075) baseStart_3813075 baseEnd_3813075 := by
    simpa [prefixWord, tailWord_3813075, baseEnd_3813075] using wordTrace_append hprefix tailTrace_3813075
  have hstable : (prefixWord ++ tailWord_3813075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813075).length < 2 ^ (prefixWord ++ tailWord_3813075).sum := by decide
  have hdescent : baseEnd_3813075 < baseStart_3813075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813076 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3813076 : Nat := 118140960795 + 3813076 * 2 ^ 59
def prefixEnd_3813076 : Nat := 4983230072969 + 3 ^ 40 * 3813076 * 2
def baseEnd_3813076 : Nat := 217548973347047617368221

theorem tailTrace_3813076 : CollatzResearch.WordTrace tailWord_3813076 prefixEnd_3813076 217548973347047617368221 := by
  unfold tailWord_3813076
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537153566942174189757541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92716204755922898919676721 69537153566942174189757541)
  ·
    refine ⟨13038216293801657660579539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69537153566942174189757541 13038216293801657660579539)
    ·
      refine ⟨19557324440702486490869309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13038216293801657660579539 19557324440702486490869309)
      ·
        refine ⟨7333996665263432434075991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19557324440702486490869309 7333996665263432434075991)
        ·
          refine ⟨11000994997895148651113987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333996665263432434075991 11000994997895148651113987)
          ·
            refine ⟨16501492496842722976670981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000994997895148651113987 16501492496842722976670981)
            ·
              refine ⟨3094029843158010558125809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16501492496842722976670981 3094029843158010558125809)
              ·
                refine ⟨2320522382368507918594357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094029843158010558125809 2320522382368507918594357)
                ·
                  refine ⟨217548973347047617368221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2320522382368507918594357 217548973347047617368221)
                  ·
                    rfl

theorem cell23_3813076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3813076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813076 prefixEnd_3813076 := by exact prefixLift 3813076
  have htrace : WordTrace (prefixWord ++ tailWord_3813076) baseStart_3813076 baseEnd_3813076 := by
    simpa [prefixWord, tailWord_3813076, baseEnd_3813076] using wordTrace_append hprefix tailTrace_3813076
  have hstable : (prefixWord ++ tailWord_3813076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813076).length < 2 ^ (prefixWord ++ tailWord_3813076).sum := by decide
  have hdescent : baseEnd_3813076 < baseStart_3813076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813112 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_3813112 : Nat := 118140960795 + 3813112 * 2 ^ 59
def prefixEnd_3813112 : Nat := 4983230072969 + 3 ^ 40 * 3813112 * 2
def baseEnd_3813112 : Nat := 1957959245426990415463823

theorem tailTrace_3813112 : CollatzResearch.WordTrace tailWord_3813112 prefixEnd_3813112 1957959245426990415463823 := by
  unfold tailWord_3813112
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537810080876963263912795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92717080107835951018550393 69537810080876963263912795)
  ·
    refine ⟨104306715121315444895869193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69537810080876963263912795 104306715121315444895869193)
    ·
      refine ⟨78230036340986583671901895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104306715121315444895869193 78230036340986583671901895)
      ·
        refine ⟨117345054511479875507852843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78230036340986583671901895 117345054511479875507852843)
        ·
          refine ⟨176017581767219813261779265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117345054511479875507852843 176017581767219813261779265)
          ·
            refine ⟨132013186325414859946334449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176017581767219813261779265 132013186325414859946334449)
            ·
              refine ⟨99009889744061144959750837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132013186325414859946334449 99009889744061144959750837)
              ·
                refine ⟨9282177163505732339976641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99009889744061144959750837 9282177163505732339976641)
                ·
                  refine ⟨6961632872629299254982481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282177163505732339976641 6961632872629299254982481)
                  ·
                    refine ⟨5221224654471974441236861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6961632872629299254982481 5221224654471974441236861)
                    ·
                      refine ⟨1957959245426990415463823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5221224654471974441236861 1957959245426990415463823)
                      ·
                        rfl

theorem cell23_3813112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_3813112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813112 prefixEnd_3813112 := by exact prefixLift 3813112
  have htrace : WordTrace (prefixWord ++ tailWord_3813112) baseStart_3813112 baseEnd_3813112 := by
    simpa [prefixWord, tailWord_3813112, baseEnd_3813112] using wordTrace_append hprefix tailTrace_3813112
  have hstable : (prefixWord ++ tailWord_3813112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813112).length < 2 ^ (prefixWord ++ tailWord_3813112).sum := by decide
  have hdescent : baseEnd_3813112 < baseStart_3813112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813119 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 1, 4]
def baseStart_3813119 : Nat := 118140960795 + 3813119 * 2 ^ 59
def prefixEnd_3813119 : Nat := 4983230072969 + 3 ^ 40 * 3813119 * 2
def baseEnd_3813119 : Nat := 652654279930523962692097

theorem tailTrace_3813119 : CollatzResearch.WordTrace tailWord_3813119 prefixEnd_3813119 652654279930523962692097 := by
  unfold tailWord_3813119
  simp only [CollatzResearch.WordTrace]
  refine ⟨139075875472728566723330411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92717250315152377815553607 139075875472728566723330411)
  ·
    refine ⟨208613813209092850084995617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139075875472728566723330411 208613813209092850084995617)
    ·
      refine ⟨156460359906819637563746713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208613813209092850084995617 156460359906819637563746713)
      ·
        refine ⟨117345269930114728172810035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156460359906819637563746713 117345269930114728172810035)
        ·
          refine ⟨176017904895172092259215053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117345269930114728172810035 176017904895172092259215053)
          ·
            refine ⟨66006714335689534597205645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176017904895172092259215053 66006714335689534597205645)
            ·
              refine ⟨24752517875883575473952117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66006714335689534597205645 24752517875883575473952117)
              ·
                refine ⟨2320548550864085200683011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24752517875883575473952117 2320548550864085200683011)
                ·
                  refine ⟨3480822826296127801024517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320548550864085200683011 3480822826296127801024517)
                  ·
                    refine ⟨652654279930523962692097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480822826296127801024517 652654279930523962692097)
                    ·
                      rfl

theorem cell23_3813119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 4].length) (baseStart_3813119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813119 prefixEnd_3813119 := by exact prefixLift 3813119
  have htrace : WordTrace (prefixWord ++ tailWord_3813119) baseStart_3813119 baseEnd_3813119 := by
    simpa [prefixWord, tailWord_3813119, baseEnd_3813119] using wordTrace_append hprefix tailTrace_3813119
  have hstable : (prefixWord ++ tailWord_3813119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813119).length < 2 ^ (prefixWord ++ tailWord_3813119).sum := by decide
  have hdescent : baseEnd_3813119 < baseStart_3813119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813122 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3813122 : Nat := 118140960795 + 3813122 * 2 ^ 59
def prefixEnd_3813122 : Nat := 4983230072969 + 3 ^ 40 * 3813122 * 2
def baseEnd_3813122 : Nat := 1957964380233535376338777

theorem tailTrace_3813122 : CollatzResearch.WordTrace tailWord_3813122 prefixEnd_3813122 1957964380233535376338777 := by
  unfold tailWord_3813122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34768996222929424558922405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92717323261145132157126413 34768996222929424558922405)
  ·
    refine ⟨6519186791799267104797951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34768996222929424558922405 6519186791799267104797951)
    ·
      refine ⟨9778780187698900657196927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6519186791799267104797951 9778780187698900657196927)
      ·
        refine ⟨14668170281548350985795391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778780187698900657196927 14668170281548350985795391)
        ·
          refine ⟨22002255422322526478693087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14668170281548350985795391 22002255422322526478693087)
          ·
            refine ⟨33003383133483789718039631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22002255422322526478693087 33003383133483789718039631)
            ·
              refine ⟨49505074700225684577059447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33003383133483789718039631 49505074700225684577059447)
              ·
                refine ⟨74257612050338526865589171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49505074700225684577059447 74257612050338526865589171)
                ·
                  refine ⟨111386418075507790298383757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74257612050338526865589171 111386418075507790298383757)
                  ·
                    refine ⟨41769906778315421361893909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111386418075507790298383757 41769906778315421361893909)
                    ·
                      refine ⟨1957964380233535376338777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41769906778315421361893909 1957964380233535376338777)
                      ·
                        rfl

theorem cell23_3813122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3813122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813122 prefixEnd_3813122 := by exact prefixLift 3813122
  have htrace : WordTrace (prefixWord ++ tailWord_3813122) baseStart_3813122 baseEnd_3813122 := by
    simpa [prefixWord, tailWord_3813122, baseEnd_3813122] using wordTrace_append hprefix tailTrace_3813122
  have hstable : (prefixWord ++ tailWord_3813122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813122).length < 2 ^ (prefixWord ++ tailWord_3813122).sum := by decide
  have hdescent : baseEnd_3813122 < baseStart_3813122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813132 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 6]
def baseStart_3813132 : Nat := 118140960795 + 3813132 * 2 ^ 59
def prefixEnd_3813132 : Nat := 4983230072969 + 3 ^ 40 * 3813132 * 2
def baseEnd_3813132 : Nat := 217552168337786704134859

theorem tailTrace_3813132 : CollatzResearch.WordTrace tailWord_3813132 prefixEnd_3813132 217552168337786704134859 := by
  unfold tailWord_3813132
  simp only [CollatzResearch.WordTrace]
  refine ⟨69538174810840734971776825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92717566414454313295702433 69538174810840734971776825)
  ·
    refine ⟨52153631108130551228832619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69538174810840734971776825 52153631108130551228832619)
    ·
      refine ⟨78230446662195826843248929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52153631108130551228832619 78230446662195826843248929)
      ·
        refine ⟨58672834996646870132436697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78230446662195826843248929 58672834996646870132436697)
        ·
          refine ⟨44004626247485152599327523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58672834996646870132436697 44004626247485152599327523)
          ·
            refine ⟨66006939371227728898991285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44004626247485152599327523 66006939371227728898991285)
            ·
              refine ⟨6188150566052599584280433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66006939371227728898991285 6188150566052599584280433)
              ·
                refine ⟨4641112924539449688210325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188150566052599584280433 4641112924539449688210325)
                ·
                  refine ⟨217552168337786704134859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4641112924539449688210325 217552168337786704134859)
                  ·
                    rfl

theorem cell23_3813132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_3813132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813132 prefixEnd_3813132 := by exact prefixLift 3813132
  have htrace : WordTrace (prefixWord ++ tailWord_3813132) baseStart_3813132 baseEnd_3813132 := by
    simpa [prefixWord, tailWord_3813132, baseEnd_3813132] using wordTrace_append hprefix tailTrace_3813132
  have hstable : (prefixWord ++ tailWord_3813132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813132).length < 2 ^ (prefixWord ++ tailWord_3813132).sum := by decide
  have hdescent : baseEnd_3813132 < baseStart_3813132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813155 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3813155 : Nat := 118140960795 + 3813155 * 2 ^ 59
def prefixEnd_3813155 : Nat := 4983230072969 + 3 ^ 40 * 3813155 * 2
def baseEnd_3813155 : Nat := 1957981325095133747226125

theorem tailTrace_3813155 : CollatzResearch.WordTrace tailWord_3813155 prefixEnd_3813155 1957981325095133747226125 := by
  unfold tailWord_3813155
  simp only [CollatzResearch.WordTrace]
  refine ⟨139077188500598144871640919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92718125667065429914427279 139077188500598144871640919)
  ·
    refine ⟨208615782750897217307461379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139077188500598144871640919 208615782750897217307461379)
    ·
      refine ⟨312923674126345825961192069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208615782750897217307461379 312923674126345825961192069)
      ·
        refine ⟨58673188898689842367723513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312923674126345825961192069 58673188898689842367723513)
        ·
          refine ⟨44004891674017381775792635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58673188898689842367723513 44004891674017381775792635)
          ·
            refine ⟨66007337511026072663688953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44004891674017381775792635 66007337511026072663688953)
            ·
              refine ⟨49505503133269554497766715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66007337511026072663688953 49505503133269554497766715)
              ·
                refine ⟨74258254699904331746650073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49505503133269554497766715 74258254699904331746650073)
                ·
                  refine ⟨55693691024928248809987555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74258254699904331746650073 55693691024928248809987555)
                  ·
                    refine ⟨83540536537392373214981333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55693691024928248809987555 83540536537392373214981333)
                    ·
                      refine ⟨1957981325095133747226125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 83540536537392373214981333 1957981325095133747226125)
                      ·
                        rfl

theorem cell23_3813155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3813155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813155 prefixEnd_3813155 := by exact prefixLift 3813155
  have htrace : WordTrace (prefixWord ++ tailWord_3813155) baseStart_3813155 baseEnd_3813155 := by
    simpa [prefixWord, tailWord_3813155, baseEnd_3813155] using wordTrace_append hprefix tailTrace_3813155
  have hstable : (prefixWord ++ tailWord_3813155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813155).length < 2 ^ (prefixWord ++ tailWord_3813155).sum := by decide
  have hdescent : baseEnd_3813155 < baseStart_3813155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813169 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_3813169 : Nat := 118140960795 + 3813169 * 2 ^ 59
def prefixEnd_3813169 : Nat := 4983230072969 + 3 ^ 40 * 3813169 * 2
def baseEnd_3813169 : Nat := 1957988513824296692451061

theorem tailTrace_3813169 : CollatzResearch.WordTrace tailWord_3813169 prefixEnd_3813169 1957988513824296692451061 := by
  unfold tailWord_3813169
  simp only [CollatzResearch.WordTrace]
  refine ⟨139077699122547425262650561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92718466081698283508433707 139077699122547425262650561)
  ·
    refine ⟨104308274341910568946987921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139077699122547425262650561 104308274341910568946987921)
    ·
      refine ⟨78231205756432926710240941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104308274341910568946987921 78231205756432926710240941)
      ·
        refine ⟨29336702158662347516340353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78231205756432926710240941 29336702158662347516340353)
        ·
          refine ⟨22002526618996760637255265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29336702158662347516340353 22002526618996760637255265)
          ·
            refine ⟨16501894964247570477941449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22002526618996760637255265 16501894964247570477941449)
            ·
              refine ⟨12376421223185677858456087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16501894964247570477941449 12376421223185677858456087)
              ·
                refine ⟨18564631834778516787684131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12376421223185677858456087 18564631834778516787684131)
                ·
                  refine ⟨27846947752167775181526197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18564631834778516787684131 27846947752167775181526197)
                  ·
                    refine ⟨2610651351765728923268081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27846947752167775181526197 2610651351765728923268081)
                    ·
                      refine ⟨1957988513824296692451061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610651351765728923268081 1957988513824296692451061)
                      ·
                        rfl

theorem cell23_3813169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_3813169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813169 prefixEnd_3813169 := by exact prefixLift 3813169
  have htrace : WordTrace (prefixWord ++ tailWord_3813169) baseStart_3813169 baseEnd_3813169 := by
    simpa [prefixWord, tailWord_3813169, baseEnd_3813169] using wordTrace_append hprefix tailTrace_3813169
  have hstable : (prefixWord ++ tailWord_3813169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813169).length < 2 ^ (prefixWord ++ tailWord_3813169).sum := by decide
  have hdescent : baseEnd_3813169 < baseStart_3813169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813193 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 1, 1, 3]
def baseStart_3813193 : Nat := 118140960795 + 3813193 * 2 ^ 59
def prefixEnd_3813193 : Nat := 4983230072969 + 3 ^ 40 * 3813193 * 2
def baseEnd_3813193 : Nat := 1958000837360004598550951

theorem tailTrace_3813193 : CollatzResearch.WordTrace tailWord_3813193 prefixEnd_3813193 1958000837360004598550951 := by
  unfold tailWord_3813193
  simp only [CollatzResearch.WordTrace]
  refine ⟨139078574474460477361524233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92719049649640318241016155 139078574474460477361524233)
  ·
    refine ⟨104308930855845358021143175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139078574474460477361524233 104308930855845358021143175)
    ·
      refine ⟨156463396283768037031714763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104308930855845358021143175 156463396283768037031714763)
      ·
        refine ⟨234695094425652055547572145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156463396283768037031714763 234695094425652055547572145)
        ·
          refine ⟨176021320819239041660679109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234695094425652055547572145 176021320819239041660679109)
          ·
            refine ⟨33003997653607320311377333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176021320819239041660679109 33003997653607320311377333)
            ·
              refine ⟨3094124780025686279191625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33003997653607320311377333 3094124780025686279191625)
              ·
                refine ⟨2320593585019264709393719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094124780025686279191625 2320593585019264709393719)
                ·
                  refine ⟨3480890377528897064090579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320593585019264709393719 3480890377528897064090579)
                  ·
                    refine ⟨5221335566293345596135869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480890377528897064090579 5221335566293345596135869)
                    ·
                      refine ⟨1958000837360004598550951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5221335566293345596135869 1958000837360004598550951)
                      ·
                        rfl

theorem cell23_3813193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 1, 3].length) (baseStart_3813193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813193 prefixEnd_3813193 := by exact prefixLift 3813193
  have htrace : WordTrace (prefixWord ++ tailWord_3813193) baseStart_3813193 baseEnd_3813193 := by
    simpa [prefixWord, tailWord_3813193, baseEnd_3813193] using wordTrace_append hprefix tailTrace_3813193
  have hstable : (prefixWord ++ tailWord_3813193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813193).length < 2 ^ (prefixWord ++ tailWord_3813193).sum := by decide
  have hdescent : baseEnd_3813193 < baseStart_3813193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813209 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_3813209 : Nat := 118140960795 + 3813209 * 2 ^ 59
def prefixEnd_3813209 : Nat := 4983230072969 + 3 ^ 40 * 3813209 * 2
def baseEnd_3813209 : Nat := 652669684350158845316959

theorem tailTrace_3813209 : CollatzResearch.WordTrace tailWord_3813209 prefixEnd_3813209 652669684350158845316959 := by
  unfold tailWord_3813209
  simp only [CollatzResearch.WordTrace]
  refine ⟨139079158042402512094106681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92719438694935008062737787 139079158042402512094106681)
  ·
    refine ⟨104309368531801884070580011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139079158042402512094106681 104309368531801884070580011)
    ·
      refine ⟨156464052797702826105870017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104309368531801884070580011 156464052797702826105870017)
      ·
        refine ⟨117348039598277119579402513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156464052797702826105870017 117348039598277119579402513)
        ·
          refine ⟨88011029698707839684551885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117348039598277119579402513 88011029698707839684551885)
          ·
            refine ⟨33004136137015439881706957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88011029698707839684551885 33004136137015439881706957)
            ·
              refine ⟨12376551051380789955640109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33004136137015439881706957 12376551051380789955640109)
              ·
                refine ⟨4641206644267796233365041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12376551051380789955640109 4641206644267796233365041)
                ·
                  refine ⟨3480904983200847175023781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641206644267796233365041 3480904983200847175023781)
                  ·
                    refine ⟨652669684350158845316959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480904983200847175023781 652669684350158845316959)
                    ·
                      rfl

theorem cell23_3813209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_3813209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813209 prefixEnd_3813209 := by exact prefixLift 3813209
  have htrace : WordTrace (prefixWord ++ tailWord_3813209) baseStart_3813209 baseEnd_3813209 := by
    simpa [prefixWord, tailWord_3813209, baseEnd_3813209] using wordTrace_append hprefix tailTrace_3813209
  have hstable : (prefixWord ++ tailWord_3813209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813209).length < 2 ^ (prefixWord ++ tailWord_3813209).sum := by decide
  have hdescent : baseEnd_3813209 < baseStart_3813209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813216 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_3813216 : Nat := 118140960795 + 3813216 * 2 ^ 59
def prefixEnd_3813216 : Nat := 4983230072969 + 3 ^ 40 * 3813216 * 2
def baseEnd_3813216 : Nat := 1958012647415058008563345

theorem tailTrace_3813216 : CollatzResearch.WordTrace tailWord_3813216 prefixEnd_3813216 1958012647415058008563345 := by
  unfold tailWord_3813216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69539706676688576144805751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92719608902251434859741001 69539706676688576144805751)
  ·
    refine ⟨104309560015032864217208627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69539706676688576144805751 104309560015032864217208627)
    ·
      refine ⟨156464340022549296325812941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104309560015032864217208627 156464340022549296325812941)
      ·
        refine ⟨58674127508455986122179853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156464340022549296325812941 58674127508455986122179853)
        ·
          refine ⟨22002797815670994795817445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58674127508455986122179853 22002797815670994795817445)
          ·
            refine ⟨4125524590438311524215771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22002797815670994795817445 4125524590438311524215771)
            ·
              refine ⟨6188286885657467286323657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125524590438311524215771 6188286885657467286323657)
              ·
                refine ⟨4641215164243100464742743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188286885657467286323657 4641215164243100464742743)
                ·
                  refine ⟨6961822746364650697114115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641215164243100464742743 6961822746364650697114115)
                  ·
                    refine ⟨10442734119546976045671173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6961822746364650697114115 10442734119546976045671173)
                    ·
                      refine ⟨1958012647415058008563345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10442734119546976045671173 1958012647415058008563345)
                      ·
                        rfl

theorem cell23_3813216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_3813216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813216 prefixEnd_3813216 := by exact prefixLift 3813216
  have htrace : WordTrace (prefixWord ++ tailWord_3813216) baseStart_3813216 baseEnd_3813216 := by
    simpa [prefixWord, tailWord_3813216, baseEnd_3813216] using wordTrace_append hprefix tailTrace_3813216
  have hstable : (prefixWord ++ tailWord_3813216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813216).length < 2 ^ (prefixWord ++ tailWord_3813216).sum := by decide
  have hdescent : baseEnd_3813216 < baseStart_3813216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813226 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3813226 : Nat := 118140960795 + 3813226 * 2 ^ 59
def prefixEnd_3813226 : Nat := 4983230072969 + 3 ^ 40 * 3813226 * 2
def baseEnd_3813226 : Nat := 652672594073867656479433

theorem tailTrace_3813226 : CollatzResearch.WordTrace tailWord_3813226 prefixEnd_3813226 652672594073867656479433 := by
  unfold tailWord_3813226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34769944520835230999368883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92719852055560615998317021 34769944520835230999368883)
  ·
    refine ⟨52154916781252846499053325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34769944520835230999368883 52154916781252846499053325)
    ·
      refine ⟨19558093792969817437144997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52154916781252846499053325 19558093792969817437144997)
      ·
        refine ⟨3667142586181840769464687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19558093792969817437144997 3667142586181840769464687)
        ·
          refine ⟨5500713879272761154197031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667142586181840769464687 5500713879272761154197031)
          ·
            refine ⟨8251070818909141731295547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500713879272761154197031 8251070818909141731295547)
            ·
              refine ⟨12376606228363712596943321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251070818909141731295547 12376606228363712596943321)
              ·
                refine ⟨9282454671272784447707491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12376606228363712596943321 9282454671272784447707491)
                ·
                  refine ⟨13923682006909176671561237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282454671272784447707491 13923682006909176671561237)
                  ·
                    refine ⟨652672594073867656479433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13923682006909176671561237 652672594073867656479433)
                    ·
                      rfl

theorem cell23_3813226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3813226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813226 prefixEnd_3813226 := by exact prefixLift 3813226
  have htrace : WordTrace (prefixWord ++ tailWord_3813226) baseStart_3813226 baseEnd_3813226 := by
    simpa [prefixWord, tailWord_3813226, baseEnd_3813226] using wordTrace_append hprefix tailTrace_3813226
  have hstable : (prefixWord ++ tailWord_3813226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813226).length < 2 ^ (prefixWord ++ tailWord_3813226).sum := by decide
  have hdescent : baseEnd_3813226 < baseStart_3813226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813233 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_3813233 : Nat := 118140960795 + 3813233 * 2 ^ 59
def prefixEnd_3813233 : Nat := 4983230072969 + 3 ^ 40 * 3813233 * 2
def baseEnd_3813233 : Nat := 1958021376586184442050767

theorem tailTrace_3813233 : CollatzResearch.WordTrace tailWord_3813233 prefixEnd_3813233 1958021376586184442050767 := by
  unfold tailWord_3813233
  simp only [CollatzResearch.WordTrace]
  refine ⟨139080033394315564192980353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92720022262877042795320235 139080033394315564192980353)
  ·
    refine ⟨104310025045736673144735265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139080033394315564192980353 104310025045736673144735265)
    ·
      refine ⟨78232518784302504858551449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104310025045736673144735265 78232518784302504858551449)
      ·
        refine ⟨58674389088226878643913587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78232518784302504858551449 58674389088226878643913587)
        ·
          refine ⟨88011583632340317965870381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58674389088226878643913587 88011583632340317965870381)
          ·
            refine ⟨33004343862127619237201393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88011583632340317965870381 33004343862127619237201393)
            ·
              refine ⟨24753257896595714427901045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33004343862127619237201393 24753257896595714427901045)
              ·
                refine ⟨2320617927805848227615723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24753257896595714427901045 2320617927805848227615723)
                ·
                  refine ⟨3480926891708772341423585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320617927805848227615723 3480926891708772341423585)
                  ·
                    refine ⟨2610695168781579256067689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480926891708772341423585 2610695168781579256067689)
                    ·
                      refine ⟨1958021376586184442050767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610695168781579256067689 1958021376586184442050767)
                      ·
                        rfl

theorem cell23_3813233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_3813233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813233 prefixEnd_3813233 := by exact prefixLift 3813233
  have htrace : WordTrace (prefixWord ++ tailWord_3813233) baseStart_3813233 baseEnd_3813233 := by
    simpa [prefixWord, tailWord_3813233, baseEnd_3813233] using wordTrace_append hprefix tailTrace_3813233
  have hstable : (prefixWord ++ tailWord_3813233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813233).length < 2 ^ (prefixWord ++ tailWord_3813233).sum := by decide
  have hdescent : baseEnd_3813233 < baseStart_3813233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813252 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3813252 : Nat := 118140960795 + 3813252 * 2 ^ 59
def prefixEnd_3813252 : Nat := 4983230072969 + 3 ^ 40 * 3813252 * 2
def baseEnd_3813252 : Nat := 652677044239539955904393

theorem tailTrace_3813252 : CollatzResearch.WordTrace tailWord_3813252 prefixEnd_3813252 652677044239539955904393 := by
  unfold tailWord_3813252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69540363190623365218961005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92720484254164486958614673 69540363190623365218961005)
  ·
    refine ⟨26077636196483761957110377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69540363190623365218961005 26077636196483761957110377)
    ·
      refine ⟨19558227147362821467832783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26077636196483761957110377 19558227147362821467832783)
      ·
        refine ⟨29337340721044232201749175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19558227147362821467832783 29337340721044232201749175)
        ·
          refine ⟨44006011081566348302623763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29337340721044232201749175 44006011081566348302623763)
          ·
            refine ⟨66009016622349522453935645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44006011081566348302623763 66009016622349522453935645)
            ·
              refine ⟨24753381233381070920225867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66009016622349522453935645 24753381233381070920225867)
              ·
                refine ⟨37130071850071606380338801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24753381233381070920225867 37130071850071606380338801)
                ·
                  refine ⟨27847553887553704785254101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37130071850071606380338801 27847553887553704785254101)
                  ·
                    refine ⟨652677044239539955904393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27847553887553704785254101 652677044239539955904393)
                    ·
                      rfl

theorem cell23_3813252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3813252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813252 prefixEnd_3813252 := by exact prefixLift 3813252
  have htrace : WordTrace (prefixWord ++ tailWord_3813252) baseStart_3813252 baseEnd_3813252 := by
    simpa [prefixWord, tailWord_3813252, baseEnd_3813252] using wordTrace_append hprefix tailTrace_3813252
  have hstable : (prefixWord ++ tailWord_3813252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813252).length < 2 ^ (prefixWord ++ tailWord_3813252).sum := by decide
  have hdescent : baseEnd_3813252 < baseStart_3813252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813256 : List Nat := [2, 1, 3, 3, 4, 1, 1, 8]
def baseStart_3813256 : Nat := 118140960795 + 3813256 * 2 ^ 59
def prefixEnd_3813256 : Nat := 4983230072969 + 3 ^ 40 * 3813256 * 2
def baseEnd_3813256 : Nat := 72519747653379179706043

theorem tailTrace_3813256 : CollatzResearch.WordTrace tailWord_3813256 prefixEnd_3813256 72519747653379179706043 := by
  unfold tailWord_3813256
  simp only [CollatzResearch.WordTrace]
  refine ⟨69540436136616119560533811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92720581515488159414045081 69540436136616119560533811)
  ·
    refine ⟨104310654204924179340800717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69540436136616119560533811 104310654204924179340800717)
    ·
      refine ⟨39116495326846567252800269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104310654204924179340800717 39116495326846567252800269)
      ·
        refine ⟨14668685747567462719800101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39116495326846567252800269 14668685747567462719800101)
        ·
          refine ⟨2750378577668899259962519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14668685747567462719800101 2750378577668899259962519)
          ·
            refine ⟨4125567866503348889943779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750378577668899259962519 4125567866503348889943779)
            ·
              refine ⟨6188351799755023334915669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125567866503348889943779 6188351799755023334915669)
              ·
                refine ⟨72519747653379179706043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6188351799755023334915669 72519747653379179706043)
                ·
                  rfl

theorem cell23_3813256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 8].length) (baseStart_3813256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813256 prefixEnd_3813256 := by exact prefixLift 3813256
  have htrace : WordTrace (prefixWord ++ tailWord_3813256) baseStart_3813256 baseEnd_3813256 := by
    simpa [prefixWord, tailWord_3813256, baseEnd_3813256] using wordTrace_append hprefix tailTrace_3813256
  have hstable : (prefixWord ++ tailWord_3813256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813256).length < 2 ^ (prefixWord ++ tailWord_3813256).sum := by decide
  have hdescent : baseEnd_3813256 < baseStart_3813256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813266 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3813266 : Nat := 118140960795 + 3813266 * 2 ^ 59
def prefixEnd_3813266 : Nat := 4983230072969 + 3 ^ 40 * 3813266 * 2
def baseEnd_3813266 : Nat := 1958038321447782812938115

theorem tailTrace_3813266 : CollatzResearch.WordTrace tailWord_3813266 prefixEnd_3813266 1958038321447782812938115 := by
  unfold tailWord_3813266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34770309250799002707232913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92720824668797340552621101 34770309250799002707232913)
  ·
    refine ⟨26077731938099252030424685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34770309250799002707232913 26077731938099252030424685)
    ·
      refine ⟨9779149476787219511409257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26077731938099252030424685 9779149476787219511409257)
      ·
        refine ⟨7334362107590414633556943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9779149476787219511409257 7334362107590414633556943)
        ·
          refine ⟨11001543161385621950335415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334362107590414633556943 11001543161385621950335415)
          ·
            refine ⟨16502314742078432925503123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001543161385621950335415 16502314742078432925503123)
            ·
              refine ⟨24753472113117649388254685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16502314742078432925503123 24753472113117649388254685)
              ·
                refine ⟨9282552042419118520595507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24753472113117649388254685 9282552042419118520595507)
                ·
                  refine ⟨13923828063628677780893261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282552042419118520595507 13923828063628677780893261)
                  ·
                    refine ⟨5221435523860754167834973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13923828063628677780893261 5221435523860754167834973)
                    ·
                      refine ⟨1958038321447782812938115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5221435523860754167834973 1958038321447782812938115)
                      ·
                        rfl

theorem cell23_3813266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3813266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813266 prefixEnd_3813266 := by exact prefixLift 3813266
  have htrace : WordTrace (prefixWord ++ tailWord_3813266) baseStart_3813266 baseEnd_3813266 := by
    simpa [prefixWord, tailWord_3813266, baseEnd_3813266] using wordTrace_append hprefix tailTrace_3813266
  have hstable : (prefixWord ++ tailWord_3813266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813266).length < 2 ^ (prefixWord ++ tailWord_3813266).sum := by decide
  have hdescent : baseEnd_3813266 < baseStart_3813266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813289 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 4, 2]
def baseStart_3813289 : Nat := 118140960795 + 3813289 * 2 ^ 59
def prefixEnd_3813289 : Nat := 4983230072969 + 3 ^ 40 * 3813289 * 2
def baseEnd_3813289 : Nat := 1958050131502836222950509

theorem tailTrace_3813289 : CollatzResearch.WordTrace tailWord_3813289 prefixEnd_3813289 1958050131502836222950509 := by
  unfold tailWord_3813289
  simp only [CollatzResearch.WordTrace]
  refine ⟨139082075882112685757018921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92721383921408457171345947 139082075882112685757018921)
  ·
    refine ⟨104311556911584514317764191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139082075882112685757018921 104311556911584514317764191)
    ·
      refine ⟨156467335367376771476646287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104311556911584514317764191 156467335367376771476646287)
      ·
        refine ⟨234701003051065157214969431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156467335367376771476646287 234701003051065157214969431)
        ·
          refine ⟨352051504576597735822454147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234701003051065157214969431 352051504576597735822454147)
          ·
            refine ⟨528077256864896603733681221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352051504576597735822454147 528077256864896603733681221)
            ·
              refine ⟨99014485662168113200065229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528077256864896603733681221 99014485662168113200065229)
              ·
                refine ⟨37130432123313042450024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99014485662168113200065229 37130432123313042450024461)
                ·
                  refine ⟨13923912046242390918759173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37130432123313042450024461 13923912046242390918759173)
                  ·
                    refine ⟨2610733508670448297267345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13923912046242390918759173 2610733508670448297267345)
                    ·
                      refine ⟨1958050131502836222950509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610733508670448297267345 1958050131502836222950509)
                      ·
                        rfl

theorem cell23_3813289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4, 2].length) (baseStart_3813289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813289 prefixEnd_3813289 := by exact prefixLift 3813289
  have htrace : WordTrace (prefixWord ++ tailWord_3813289) baseStart_3813289 baseEnd_3813289 := by
    simpa [prefixWord, tailWord_3813289, baseEnd_3813289] using wordTrace_append hprefix tailTrace_3813289
  have hstable : (prefixWord ++ tailWord_3813289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813289).length < 2 ^ (prefixWord ++ tailWord_3813289).sum := by decide
  have hdescent : baseEnd_3813289 < baseStart_3813289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813294 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3813294 : Nat := 118140960795 + 3813294 * 2 ^ 59
def prefixEnd_3813294 : Nat := 4983230072969 + 3 ^ 40 * 3813294 * 2
def baseEnd_3813294 : Nat := 652684232968702901129329

theorem tailTrace_3813294 : CollatzResearch.WordTrace tailWord_3813294 prefixEnd_3813294 652684232968702901129329 := by
  unfold tailWord_3813294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385282280886821451368867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92721505498063047740633957 17385282280886821451368867)
  ·
    refine ⟨26077923421330232177053301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17385282280886821451368867 26077923421330232177053301)
    ·
      refine ⟨2444805320749709266598747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26077923421330232177053301 2444805320749709266598747)
      ·
        refine ⟨3667207981124563899898121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444805320749709266598747 3667207981124563899898121)
        ·
          refine ⟨2750405985843422924923591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3667207981124563899898121 2750405985843422924923591)
          ·
            refine ⟨4125608978765134387385387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750405985843422924923591 4125608978765134387385387)
            ·
              refine ⟨6188413468147701581078081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125608978765134387385387 6188413468147701581078081)
              ·
                refine ⟨4641310101110776185808561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188413468147701581078081 4641310101110776185808561)
                ·
                  refine ⟨3480982575833082139356421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641310101110776185808561 3480982575833082139356421)
                  ·
                    refine ⟨652684232968702901129329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3480982575833082139356421 652684232968702901129329)
                    ·
                      rfl

theorem cell23_3813294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3813294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813294 prefixEnd_3813294 := by exact prefixLift 3813294
  have htrace : WordTrace (prefixWord ++ tailWord_3813294) baseStart_3813294 baseEnd_3813294 := by
    simpa [prefixWord, tailWord_3813294, baseEnd_3813294] using wordTrace_append hprefix tailTrace_3813294
  have hstable : (prefixWord ++ tailWord_3813294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813294).length < 2 ^ (prefixWord ++ tailWord_3813294).sum := by decide
  have hdescent : baseEnd_3813294 < baseStart_3813294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813300 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3813300 : Nat := 118140960795 + 3813300 * 2 ^ 59
def prefixEnd_3813300 : Nat := 4983230072969 + 3 ^ 40 * 3813300 * 2
def baseEnd_3813300 : Nat := 1958055779790035679912959

theorem tailTrace_3813300 : CollatzResearch.WordTrace tailWord_3813300 prefixEnd_3813300 1958055779790035679912959 := by
  unfold tailWord_3813300
  simp only [CollatzResearch.WordTrace]
  refine ⟨69541238542536417317834677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92721651390048556423779569 69541238542536417317834677)
  ·
    refine ⟨6519491113362789123547001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69541238542536417317834677 6519491113362789123547001)
    ·
      refine ⟨4889618335022091842660251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519491113362789123547001 4889618335022091842660251)
      ·
        refine ⟨7334427502533137763990377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889618335022091842660251 7334427502533137763990377)
        ·
          refine ⟨5500820626899853322992783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7334427502533137763990377 5500820626899853322992783)
          ·
            refine ⟨8251230940349779984489175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500820626899853322992783 8251230940349779984489175)
            ·
              refine ⟨12376846410524669976733763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251230940349779984489175 12376846410524669976733763)
              ·
                refine ⟨18565269615787004965100645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12376846410524669976733763 18565269615787004965100645)
                ·
                  refine ⟨3480988052960063430956371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18565269615787004965100645 3480988052960063430956371)
                  ·
                    refine ⟨5221482079440095146434557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3480988052960063430956371 5221482079440095146434557)
                    ·
                      refine ⟨1958055779790035679912959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5221482079440095146434557 1958055779790035679912959)
                      ·
                        rfl

theorem cell23_3813300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3813300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813300 prefixEnd_3813300 := by exact prefixLift 3813300
  have htrace : WordTrace (prefixWord ++ tailWord_3813300) baseStart_3813300 baseEnd_3813300 := by
    simpa [prefixWord, tailWord_3813300, baseEnd_3813300] using wordTrace_append hprefix tailTrace_3813300
  have hstable : (prefixWord ++ tailWord_3813300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813300).length < 2 ^ (prefixWord ++ tailWord_3813300).sum := by decide
  have hdescent : baseEnd_3813300 < baseStart_3813300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813359 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 2, 5]
def baseStart_3813359 : Nat := 118140960795 + 3813359 * 2 ^ 59
def prefixEnd_3813359 : Nat := 4983230072969 + 3 ^ 40 * 3813359 * 2
def baseEnd_3813359 : Nat := 652695358382883649691729

theorem tailTrace_3813359 : CollatzResearch.WordTrace tailWord_3813359 prefixEnd_3813359 652695358382883649691729 := by
  unfold tailWord_3813359
  simp only [CollatzResearch.WordTrace]
  refine ⟨139084628991859087712067131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92723085994572725141378087 139084628991859087712067131)
  ·
    refine ⟨208626943487788631568100697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139084628991859087712067131 208626943487788631568100697)
    ·
      refine ⟨156470207615841473676075523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208626943487788631568100697 156470207615841473676075523)
      ·
        refine ⟨234705311423762210514113285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156470207615841473676075523 234705311423762210514113285)
        ·
          refine ⟨44007245891955414471396241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234705311423762210514113285 44007245891955414471396241)
          ·
            refine ⟨33005434418966560853547181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44007245891955414471396241 33005434418966560853547181)
            ·
              refine ⟨12377037907112460320080193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33005434418966560853547181 12377037907112460320080193)
              ·
                refine ⟨9282778430334345240060145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12377037907112460320080193 9282778430334345240060145)
                ·
                  refine ⟨6962083822750758930045109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282778430334345240060145 6962083822750758930045109)
                  ·
                    refine ⟨652695358382883649691729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962083822750758930045109 652695358382883649691729)
                    ·
                      rfl

theorem cell23_3813359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_3813359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813359 prefixEnd_3813359 := by exact prefixLift 3813359
  have htrace : WordTrace (prefixWord ++ tailWord_3813359) baseStart_3813359 baseEnd_3813359 := by
    simpa [prefixWord, tailWord_3813359, baseEnd_3813359] using wordTrace_append hprefix tailTrace_3813359
  have hstable : (prefixWord ++ tailWord_3813359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813359).length < 2 ^ (prefixWord ++ tailWord_3813359).sum := by decide
  have hdescent : baseEnd_3813359 < baseStart_3813359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813369 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3813369 : Nat := 118140960795 + 3813369 * 2 ^ 59
def prefixEnd_3813369 : Nat := 4983230072969 + 3 ^ 40 * 3813369 * 2
def baseEnd_3813369 : Nat := 1958091209955195909950141

theorem tailTrace_3813369 : CollatzResearch.WordTrace tailWord_3813369 prefixEnd_3813369 1958091209955195909950141 := by
  unfold tailWord_3813369
  simp only [CollatzResearch.WordTrace]
  refine ⟨139084993721822859419931161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92723329147881906279954107 139084993721822859419931161)
  ·
    refine ⟨104313745291367144564948371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139084993721822859419931161 104313745291367144564948371)
    ·
      refine ⟨156470617937050716847422557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104313745291367144564948371 156470617937050716847422557)
      ·
        refine ⟨58676481726394018817783459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156470617937050716847422557 58676481726394018817783459)
        ·
          refine ⟨88014722589591028226675189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58676481726394018817783459 88014722589591028226675189)
          ·
            refine ⟨8251380242774158896250799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88014722589591028226675189 8251380242774158896250799)
            ·
              refine ⟨12377070364161238344376199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8251380242774158896250799 12377070364161238344376199)
              ·
                refine ⟨18565605546241857516564299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377070364161238344376199 18565605546241857516564299)
                ·
                  refine ⟨27848408319362786274846449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18565605546241857516564299 27848408319362786274846449)
                  ·
                    refine ⟨20886306239522089706134837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27848408319362786274846449 20886306239522089706134837)
                    ·
                      refine ⟨1958091209955195909950141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20886306239522089706134837 1958091209955195909950141)
                      ·
                        rfl

theorem cell23_3813369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3813369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813369 prefixEnd_3813369 := by exact prefixLift 3813369
  have htrace : WordTrace (prefixWord ++ tailWord_3813369) baseStart_3813369 baseEnd_3813369 := by
    simpa [prefixWord, tailWord_3813369, baseEnd_3813369] using wordTrace_append hprefix tailTrace_3813369
  have hstable : (prefixWord ++ tailWord_3813369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813369).length < 2 ^ (prefixWord ++ tailWord_3813369).sum := by decide
  have hdescent : baseEnd_3813369 < baseStart_3813369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813374 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3813374 : Nat := 118140960795 + 3813374 * 2 ^ 59
def prefixEnd_3813374 : Nat := 4983230072969 + 3 ^ 40 * 3813374 * 2
def baseEnd_3813374 : Nat := 1958093777358468390387619

theorem tailTrace_3813374 : CollatzResearch.WordTrace tailWord_3813374 prefixEnd_3813374 1958093777358468390387619 := by
  unfold tailWord_3813374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385647010850593159232897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92723450724536496849242117 17385647010850593159232897)
  ·
    refine ⟨13039235258137944869424673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17385647010850593159232897 13039235258137944869424673)
    ·
      refine ⟨9779426443603458652068505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13039235258137944869424673 9779426443603458652068505)
      ·
        refine ⟨7334569832702593989051379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9779426443603458652068505 7334569832702593989051379)
        ·
          refine ⟨11001854749053890983577069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334569832702593989051379 11001854749053890983577069)
          ·
            refine ⟨4125695530895209118841401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11001854749053890983577069 4125695530895209118841401)
            ·
              refine ⟨3094271648171406839131051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4125695530895209118841401 3094271648171406839131051)
              ·
                refine ⟨4641407472257110258696577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094271648171406839131051 4641407472257110258696577)
                ·
                  refine ⟨3481055604192832694022433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641407472257110258696577 3481055604192832694022433)
                  ·
                    refine ⟨2610791703144624520516825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3481055604192832694022433 2610791703144624520516825)
                    ·
                      refine ⟨1958093777358468390387619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2610791703144624520516825 1958093777358468390387619)
                      ·
                        rfl

theorem cell23_3813374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3813374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813374 prefixEnd_3813374 := by exact prefixLift 3813374
  have htrace : WordTrace (prefixWord ++ tailWord_3813374) baseStart_3813374 baseEnd_3813374 := by
    simpa [prefixWord, tailWord_3813374, baseEnd_3813374] using wordTrace_append hprefix tailTrace_3813374
  have hstable : (prefixWord ++ tailWord_3813374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813374).length < 2 ^ (prefixWord ++ tailWord_3813374).sum := by decide
  have hdescent : baseEnd_3813374 < baseStart_3813374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813449 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_3813449 : Nat := 118140960795 + 3813449 * 2 ^ 59
def prefixEnd_3813449 : Nat := 4983230072969 + 3 ^ 40 * 3813449 * 2
def baseEnd_3813449 : Nat := 652710762802518532316591

theorem tailTrace_3813449 : CollatzResearch.WordTrace tailWord_3813449 prefixEnd_3813449 652710762802518532316591 := by
  unfold tailWord_3813449
  simp only [CollatzResearch.WordTrace]
  refine ⟨139087911561533033082843401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92725274374355355388562267 139087911561533033082843401)
  ·
    refine ⟨104315933671149774812132551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139087911561533033082843401 104315933671149774812132551)
    ·
      refine ⟨156473900506724662218198827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104315933671149774812132551 156473900506724662218198827)
      ·
        refine ⟨234710850760086993327298241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156473900506724662218198827 234710850760086993327298241)
        ·
          refine ⟨176033138070065244995473681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234710850760086993327298241 176033138070065244995473681)
          ·
            refine ⟨132024853552548933746605261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176033138070065244995473681 132024853552548933746605261)
            ·
              refine ⟨49509320082205850154976973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132024853552548933746605261 49509320082205850154976973)
              ·
                refine ⟨18565995030827193808116365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49509320082205850154976973 18565995030827193808116365)
                ·
                  refine ⟨6962248136560197678043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18565995030827193808116365 6962248136560197678043637)
                  ·
                    refine ⟨652710762802518532316591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962248136560197678043637 652710762802518532316591)
                    ·
                      rfl

theorem cell23_3813449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_3813449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813449 prefixEnd_3813449 := by exact prefixLift 3813449
  have htrace : WordTrace (prefixWord ++ tailWord_3813449) baseStart_3813449 baseEnd_3813449 := by
    simpa [prefixWord, tailWord_3813449, baseEnd_3813449] using wordTrace_append hprefix tailTrace_3813449
  have hstable : (prefixWord ++ tailWord_3813449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813449).length < 2 ^ (prefixWord ++ tailWord_3813449).sum := by decide
  have hdescent : baseEnd_3813449 < baseStart_3813449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813466 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_3813466 : Nat := 118140960795 + 3813466 * 2 ^ 59
def prefixEnd_3813466 : Nat := 4983230072969 + 3 ^ 40 * 3813466 * 2
def baseEnd_3813466 : Nat := 652713672526227343479065

theorem tailTrace_3813466 : CollatzResearch.WordTrace tailWord_3813466 prefixEnd_3813466 652713672526227343479065 := by
  unfold tailWord_3813466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772132900617861246553063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92725687734980963324141501 34772132900617861246553063)
  ·
    refine ⟨52158199350926791869829595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34772132900617861246553063 52158199350926791869829595)
    ·
      refine ⟨78237299026390187804744393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52158199350926791869829595 78237299026390187804744393)
      ·
        refine ⟨58677974269792640853558295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78237299026390187804744393 58677974269792640853558295)
        ·
          refine ⟨88016961404688961280337443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58677974269792640853558295 88016961404688961280337443)
          ·
            refine ⟨132025442107033441920506165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88016961404688961280337443 132025442107033441920506165)
            ·
              refine ⟨12377385197534385180047453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132025442107033441920506165 12377385197534385180047453)
              ·
                refine ⟨4641519449075394442517795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12377385197534385180047453 4641519449075394442517795)
                ·
                  refine ⟨6962279173613091663776693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641519449075394442517795 6962279173613091663776693)
                  ·
                    refine ⟨652713672526227343479065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6962279173613091663776693 652713672526227343479065)
                    ·
                      rfl

theorem cell23_3813466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_3813466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3813466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3813466 prefixEnd_3813466 := by exact prefixLift 3813466
  have htrace : WordTrace (prefixWord ++ tailWord_3813466) baseStart_3813466 baseEnd_3813466 := by
    simpa [prefixWord, tailWord_3813466, baseEnd_3813466] using wordTrace_append hprefix tailTrace_3813466
  have hstable : (prefixWord ++ tailWord_3813466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813466).length < 2 ^ (prefixWord ++ tailWord_3813466).sum := by decide
  have hdescent : baseEnd_3813466 < baseStart_3813466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
