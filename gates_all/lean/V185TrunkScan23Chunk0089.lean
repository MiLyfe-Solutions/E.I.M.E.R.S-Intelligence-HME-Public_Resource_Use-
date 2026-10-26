import V185TrunkScan23Chunk0088

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_528352 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_528352 : Nat := 118140960795 + 528352 * 2 ^ 59
def prefixEnd_528352 : Nat := 4983230072969 + 3 ^ 40 * 528352 * 2
def baseEnd_528352 : Nat := 90432843588140684690053

theorem tailTrace_528352 : CollatzResearch.WordTrace tailWord_528352 prefixEnd_528352 90432843588140684690053 := by
  unfold tailWord_528352
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635290290939207091353655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12847053721252276121804873 9635290290939207091353655)
  ·
    refine ⟨14452935436408810637030483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635290290939207091353655 14452935436408810637030483)
    ·
      refine ⟨21679403154613215955545725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14452935436408810637030483 21679403154613215955545725)
      ·
        refine ⟨8129776182979955983329647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21679403154613215955545725 8129776182979955983329647)
        ·
          refine ⟨12194664274469933974994471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8129776182979955983329647 12194664274469933974994471)
          ·
            refine ⟨18291996411704900962491707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12194664274469933974994471 18291996411704900962491707)
            ·
              refine ⟨27437994617557351443737561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18291996411704900962491707 27437994617557351443737561)
              ·
                refine ⟨20578495963168013582803171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27437994617557351443737561 20578495963168013582803171)
                ·
                  refine ⟨30867743944752020374204757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20578495963168013582803171 30867743944752020374204757)
                  ·
                    refine ⟨90432843588140684690053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 30867743944752020374204757 90432843588140684690053)
                    ·
                      rfl

theorem cell23_528352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_528352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528352 prefixEnd_528352 := by exact prefixLift 528352
  have htrace : WordTrace (prefixWord ++ tailWord_528352) baseStart_528352 baseEnd_528352 := by
    simpa [prefixWord, tailWord_528352, baseEnd_528352] using wordTrace_append hprefix tailTrace_528352
  have hstable : (prefixWord ++ tailWord_528352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528352).length < 2 ^ (prefixWord ++ tailWord_528352).sum := by decide
  have hdescent : baseEnd_528352 < baseStart_528352 := by decide
  rcases family_descends (prefixWord ++ tailWord_528352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528354 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_528354 : Nat := 118140960795 + 528354 * 2 ^ 59
def prefixEnd_528354 : Nat := 4983230072969 + 3 ^ 40 * 528354 * 2
def baseEnd_528354 : Nat := 271299557725731046245151

theorem tailTrace_528354 : CollatzResearch.WordTrace tailWord_528354 prefixEnd_528354 271299557725731046245151 := by
  unfold tailWord_528354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4817663381967792131070029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12847102351914112349520077 4817663381967792131070029)
  ·
    refine ⟨1806623768237922049151261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4817663381967792131070029 1806623768237922049151261)
    ·
      refine ⟨677483913089220768431723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1806623768237922049151261 677483913089220768431723)
      ·
        refine ⟨1016225869633831152647585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677483913089220768431723 1016225869633831152647585)
        ·
          refine ⟨762169402225373364485689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016225869633831152647585 762169402225373364485689)
          ·
            refine ⟨571627051669030023364267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762169402225373364485689 571627051669030023364267)
            ·
              refine ⟨857440577503545035046401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571627051669030023364267 857440577503545035046401)
              ·
                refine ⟨643080433127658776284801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857440577503545035046401 643080433127658776284801)
                ·
                  refine ⟨482310324845744082213601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643080433127658776284801 482310324845744082213601)
                  ·
                    refine ⟨361732743634308061660201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482310324845744082213601 361732743634308061660201)
                    ·
                      refine ⟨271299557725731046245151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361732743634308061660201 271299557725731046245151)
                      ·
                        rfl

theorem cell23_528354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_528354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528354 prefixEnd_528354 := by exact prefixLift 528354
  have htrace : WordTrace (prefixWord ++ tailWord_528354) baseStart_528354 baseEnd_528354 := by
    simpa [prefixWord, tailWord_528354, baseEnd_528354] using wordTrace_append hprefix tailTrace_528354
  have hstable : (prefixWord ++ tailWord_528354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528354).length < 2 ^ (prefixWord ++ tailWord_528354).sum := by decide
  have hdescent : baseEnd_528354 < baseStart_528354 := by decide
  rcases family_descends (prefixWord ++ tailWord_528354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528376 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_528376 : Nat := 118140960795 + 528376 * 2 ^ 59
def prefixEnd_528376 : Nat := 4983230072969 + 3 ^ 40 * 528376 * 2
def baseEnd_528376 : Nat := 271310854300129960170049

theorem tailTrace_528376 : CollatzResearch.WordTrace tailWord_528376 prefixEnd_528376 271310854300129960170049 := by
  unfold tailWord_528376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635727966895733140790491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12847637289194310854387321 9635727966895733140790491)
  ·
    refine ⟨14453591950343599711185737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635727966895733140790491 14453591950343599711185737)
    ·
      refine ⟨10840193962757699783389303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14453591950343599711185737 10840193962757699783389303)
      ·
        refine ⟨16260290944136549675083955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10840193962757699783389303 16260290944136549675083955)
        ·
          refine ⟨24390436416204824512625933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16260290944136549675083955 24390436416204824512625933)
          ·
            refine ⟨9146413656076809192234725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24390436416204824512625933 9146413656076809192234725)
            ·
              refine ⟨1714952560514401723544011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9146413656076809192234725 1714952560514401723544011)
              ·
                refine ⟨2572428840771602585316017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1714952560514401723544011 2572428840771602585316017)
                ·
                  refine ⟨1929321630578701938987013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2572428840771602585316017 1929321630578701938987013)
                  ·
                    refine ⟨361747805733506613560065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1929321630578701938987013 361747805733506613560065)
                    ·
                      refine ⟨271310854300129960170049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361747805733506613560065 271310854300129960170049)
                      ·
                        rfl

theorem cell23_528376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_528376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528376 prefixEnd_528376 := by exact prefixLift 528376
  have htrace : WordTrace (prefixWord ++ tailWord_528376) baseStart_528376 baseEnd_528376 := by
    simpa [prefixWord, tailWord_528376, baseEnd_528376] using wordTrace_append hprefix tailTrace_528376
  have hstable : (prefixWord ++ tailWord_528376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528376).length < 2 ^ (prefixWord ++ tailWord_528376).sum := by decide
  have hdescent : baseEnd_528376 < baseStart_528376 := by decide
  rcases family_descends (prefixWord ++ tailWord_528376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528379 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3]
def baseStart_528379 : Nat := 118140960795 + 528379 * 2 ^ 59
def prefixEnd_528379 : Nat := 4983230072969 + 3 ^ 40 * 528379 * 2
def baseEnd_528379 : Nat := 271312394742093448432535

theorem tailTrace_528379 : CollatzResearch.WordTrace tailWord_528379 prefixEnd_528379 271312394742093448432535 := by
  unfold tailWord_528379
  simp only [CollatzResearch.WordTrace]
  refine ⟨19271565352780597793940191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12847710235187065195960127 19271565352780597793940191)
  ·
    refine ⟨28907348029170896690910287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19271565352780597793940191 28907348029170896690910287)
    ·
      refine ⟨43361022043756345036365431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28907348029170896690910287 43361022043756345036365431)
      ·
        refine ⟨65041533065634517554548147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43361022043756345036365431 65041533065634517554548147)
        ·
          refine ⟨97562299598451776331822221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65041533065634517554548147 97562299598451776331822221)
          ·
            refine ⟨36585862349419416124433333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97562299598451776331822221 36585862349419416124433333)
            ·
              refine ⟨3429924595258070261665625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36585862349419416124433333 3429924595258070261665625)
              ·
                refine ⟨2572443446443552696249219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429924595258070261665625 2572443446443552696249219)
                ·
                  refine ⟨3858665169665329044373829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572443446443552696249219 3858665169665329044373829)
                  ·
                    refine ⟨723499719312249195820093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858665169665329044373829 723499719312249195820093)
                    ·
                      refine ⟨271312394742093448432535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723499719312249195820093 271312394742093448432535)
                      ·
                        rfl

theorem cell23_528379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 3].length) (baseStart_528379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528379 prefixEnd_528379 := by exact prefixLift 528379
  have htrace : WordTrace (prefixWord ++ tailWord_528379) baseStart_528379 baseEnd_528379 := by
    simpa [prefixWord, tailWord_528379, baseEnd_528379] using wordTrace_append hprefix tailTrace_528379
  have hstable : (prefixWord ++ tailWord_528379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528379).length < 2 ^ (prefixWord ++ tailWord_528379).sum := by decide
  have hdescent : baseEnd_528379 < baseStart_528379 := by decide
  rcases family_descends (prefixWord ++ tailWord_528379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528396 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_528396 : Nat := 118140960795 + 528396 * 2 ^ 59
def prefixEnd_528396 : Nat := 4983230072969 + 3 ^ 40 * 528396 * 2
def baseEnd_528396 : Nat := 271321123913219881919957

theorem tailTrace_528396 : CollatzResearch.WordTrace tailWord_528396 prefixEnd_528396 271321123913219881919957 := by
  unfold tailWord_528396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636092696859504848654521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12848123595812673131539361 9636092696859504848654521)
  ·
    refine ⟨7227069522644628636490891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9636092696859504848654521 7227069522644628636490891)
    ·
      refine ⟨10840604283966942954736337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7227069522644628636490891 10840604283966942954736337)
      ·
        refine ⟨8130453212975207216052253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10840604283966942954736337 8130453212975207216052253)
        ·
          refine ⟨3048919954865702706019595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8130453212975207216052253 3048919954865702706019595)
          ·
            refine ⟨4573379932298554059029393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048919954865702706019595 4573379932298554059029393)
            ·
              refine ⟨3430034949223915544272045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4573379932298554059029393 3430034949223915544272045)
              ·
                refine ⟨1286263105958968329102017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430034949223915544272045 1286263105958968329102017)
                ·
                  refine ⟨964697329469226246826513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286263105958968329102017 964697329469226246826513)
                  ·
                    refine ⟨723522997101919685119885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964697329469226246826513 723522997101919685119885)
                    ·
                      refine ⟨271321123913219881919957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723522997101919685119885 271321123913219881919957)
                      ·
                        rfl

theorem cell23_528396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_528396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528396 prefixEnd_528396 := by exact prefixLift 528396
  have htrace : WordTrace (prefixWord ++ tailWord_528396) baseStart_528396 baseEnd_528396 := by
    simpa [prefixWord, tailWord_528396, baseEnd_528396] using wordTrace_append hprefix tailTrace_528396
  have hstable : (prefixWord ++ tailWord_528396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528396).length < 2 ^ (prefixWord ++ tailWord_528396).sum := by decide
  have hdescent : baseEnd_528396 < baseStart_528396 := by decide
  rcases family_descends (prefixWord ++ tailWord_528396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528403 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 1, 4]
def baseStart_528403 : Nat := 118140960795 + 528403 * 2 ^ 59
def prefixEnd_528403 : Nat := 4983230072969 + 3 ^ 40 * 528403 * 2
def baseEnd_528403 : Nat := 90441572759267118177475

theorem tailTrace_528403 : CollatzResearch.WordTrace tailWord_528403 prefixEnd_528403 90441572759267118177475 := by
  unfold tailWord_528403
  simp only [CollatzResearch.WordTrace]
  refine ⟨19272440704693649892813863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12848293803129099928542575 19272440704693649892813863)
  ·
    refine ⟨28908661057040474839220795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19272440704693649892813863 28908661057040474839220795)
    ·
      refine ⟨43362991585560712258831193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28908661057040474839220795 43362991585560712258831193)
      ·
        refine ⟨32522243689170534194123395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43362991585560712258831193 32522243689170534194123395)
        ·
          refine ⟨48783365533755801291185093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32522243689170534194123395 48783365533755801291185093)
          ·
            refine ⟨9146881037579212742097205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48783365533755801291185093 9146881037579212742097205)
            ·
              refine ⟨857520097273051194571613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9146881037579212742097205 857520097273051194571613)
              ·
                refine ⟨321570036477394197964355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857520097273051194571613 321570036477394197964355)
                ·
                  refine ⟨482355054716091296946533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321570036477394197964355 482355054716091296946533)
                  ·
                    refine ⟨90441572759267118177475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482355054716091296946533 90441572759267118177475)
                    ·
                      rfl

theorem cell23_528403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 1, 4].length) (baseStart_528403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528403 prefixEnd_528403 := by exact prefixLift 528403
  have htrace : WordTrace (prefixWord ++ tailWord_528403) baseStart_528403 baseEnd_528403 := by
    simpa [prefixWord, tailWord_528403, baseEnd_528403] using wordTrace_append hprefix tailTrace_528403
  have hstable : (prefixWord ++ tailWord_528403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528403).length < 2 ^ (prefixWord ++ tailWord_528403).sum := by decide
  have hdescent : baseEnd_528403 < baseStart_528403 := by decide
  rcases family_descends (prefixWord ++ tailWord_528403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528413 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_528413 : Nat := 118140960795 + 528413 * 2 ^ 59
def prefixEnd_528413 : Nat := 4983230072969 + 3 ^ 40 * 528413 * 2
def baseEnd_528413 : Nat := 271329853084346315407379

theorem tailTrace_528413 : CollatzResearch.WordTrace tailWord_528413 prefixEnd_528413 271329853084346315407379 := by
  unfold tailWord_528413
  simp only [CollatzResearch.WordTrace]
  refine ⟨19272805434657421600677893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12848536956438281067118595 19272805434657421600677893)
  ·
    refine ⟨3613651018998266550127105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19272805434657421600677893 3613651018998266550127105)
    ·
      refine ⟨2710238264248699912595329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3613651018998266550127105 2710238264248699912595329)
      ·
        refine ⟨2032678698186524934446497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2710238264248699912595329 2032678698186524934446497)
        ·
          refine ⟨1524509023639893700834873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032678698186524934446497 1524509023639893700834873)
          ·
            refine ⟨1143381767729920275626155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524509023639893700834873 1143381767729920275626155)
            ·
              refine ⟨1715072651594880413439233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143381767729920275626155 1715072651594880413439233)
              ·
                refine ⟨1286304488696160310079425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1715072651594880413439233 1286304488696160310079425)
                ·
                  refine ⟨964728366522120232559569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286304488696160310079425 964728366522120232559569)
                  ·
                    refine ⟨723546274891590174419677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964728366522120232559569 723546274891590174419677)
                    ·
                      refine ⟨271329853084346315407379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723546274891590174419677 271329853084346315407379)
                      ·
                        rfl

theorem cell23_528413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_528413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528413 prefixEnd_528413 := by exact prefixLift 528413
  have htrace : WordTrace (prefixWord ++ tailWord_528413) baseStart_528413 baseEnd_528413 := by
    simpa [prefixWord, tailWord_528413, baseEnd_528413] using wordTrace_append hprefix tailTrace_528413
  have hstable : (prefixWord ++ tailWord_528413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528413).length < 2 ^ (prefixWord ++ tailWord_528413).sum := by decide
  have hdescent : baseEnd_528413 < baseStart_528413 := by decide
  rcases family_descends (prefixWord ++ tailWord_528413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528420 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_528420 : Nat := 118140960795 + 528420 * 2 ^ 59
def prefixEnd_528420 : Nat := 4983230072969 + 3 ^ 40 * 528420 * 2
def baseEnd_528420 : Nat := 90444482482975929339949

theorem tailTrace_528420 : CollatzResearch.WordTrace tailWord_528420 prefixEnd_528420 90444482482975929339949 := by
  unfold tailWord_528420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636530372816030898091357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12848707163754707864121809 9636530372816030898091357)
  ·
    refine ⟨3613698889806011586784259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9636530372816030898091357 3613698889806011586784259)
    ·
      refine ⟨5420548334709017380176389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613698889806011586784259 5420548334709017380176389)
      ·
        refine ⟨1016352812757940758783073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5420548334709017380176389 1016352812757940758783073)
        ·
          refine ⟨762264609568455569087305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016352812757940758783073 762264609568455569087305)
          ·
            refine ⟨571698457176341676815479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762264609568455569087305 571698457176341676815479)
            ·
              refine ⟨857547685764512515223219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571698457176341676815479 857547685764512515223219)
              ·
                refine ⟨1286321528646768772834829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857547685764512515223219 1286321528646768772834829)
                ·
                  refine ⟨482370573242538289813061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1286321528646768772834829 482370573242538289813061)
                  ·
                    refine ⟨90444482482975929339949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482370573242538289813061 90444482482975929339949)
                    ·
                      rfl

theorem cell23_528420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_528420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528420 prefixEnd_528420 := by exact prefixLift 528420
  have htrace : WordTrace (prefixWord ++ tailWord_528420) baseStart_528420 baseEnd_528420 := by
    simpa [prefixWord, tailWord_528420, baseEnd_528420] using wordTrace_append hprefix tailTrace_528420
  have hstable : (prefixWord ++ tailWord_528420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528420).length < 2 ^ (prefixWord ++ tailWord_528420).sum := by decide
  have hdescent : baseEnd_528420 < baseStart_528420 := by decide
  rcases family_descends (prefixWord ++ tailWord_528420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528433 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 6]
def baseStart_528433 : Nat := 118140960795 + 528433 * 2 ^ 59
def prefixEnd_528433 : Nat := 4983230072969 + 3 ^ 40 * 528433 * 2
def baseEnd_528433 : Nat := 30148902521937359684143

theorem tailTrace_528433 : CollatzResearch.WordTrace tailWord_528433 prefixEnd_528433 30148902521937359684143 := by
  unfold tailWord_528433
  simp only [CollatzResearch.WordTrace]
  refine ⟨19273534894584965016405953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12849023263056643344270635 19273534894584965016405953)
  ·
    refine ⟨14455151170938723762304465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19273534894584965016405953 14455151170938723762304465)
    ·
      refine ⟨10841363378204042821728349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14455151170938723762304465 10841363378204042821728349)
      ·
        refine ⟨4065511266826516058148131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10841363378204042821728349 4065511266826516058148131)
        ·
          refine ⟨6098266900239774087222197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065511266826516058148131 6098266900239774087222197)
          ·
            refine ⟨571712521897478820677081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6098266900239774087222197 571712521897478820677081)
            ·
              refine ⟨428784391423109115507811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571712521897478820677081 428784391423109115507811)
              ·
                refine ⟨643176587134663673261717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428784391423109115507811 643176587134663673261717)
                ·
                  refine ⟨30148902521937359684143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 643176587134663673261717 30148902521937359684143)
                  ·
                    rfl

theorem cell23_528433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 6].length) (baseStart_528433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528433 prefixEnd_528433 := by exact prefixLift 528433
  have htrace : WordTrace (prefixWord ++ tailWord_528433) baseStart_528433 baseEnd_528433 := by
    simpa [prefixWord, tailWord_528433, baseEnd_528433] using wordTrace_append hprefix tailTrace_528433
  have hstable : (prefixWord ++ tailWord_528433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528433).length < 2 ^ (prefixWord ++ tailWord_528433).sum := by decide
  have hdescent : baseEnd_528433 < baseStart_528433 := by decide
  rcases family_descends (prefixWord ++ tailWord_528433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528459 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 1, 6]
def baseStart_528459 : Nat := 118140960795 + 528459 * 2 ^ 59
def prefixEnd_528459 : Nat := 4983230072969 + 3 ^ 40 * 528459 * 2
def baseEnd_528459 : Nat := 90451157731484378477389

theorem tailTrace_528459 : CollatzResearch.WordTrace tailWord_528459 prefixEnd_528459 90451157731484378477389 := by
  unfold tailWord_528459
  simp only [CollatzResearch.WordTrace]
  refine ⟨19274483192490771456852431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12849655461660514304568287 19274483192490771456852431)
  ·
    refine ⟨28911724788736157185278647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19274483192490771456852431 28911724788736157185278647)
    ·
      refine ⟨43367587183104235777917971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28911724788736157185278647 43367587183104235777917971)
      ·
        refine ⟨65051380774656353666876957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43367587183104235777917971 65051380774656353666876957)
        ·
          refine ⟨24394267790496132625078859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65051380774656353666876957 24394267790496132625078859)
          ·
            refine ⟨36591401685744198937618289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24394267790496132625078859 36591401685744198937618289)
            ·
              refine ⟨27443551264308149203213717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36591401685744198937618289 27443551264308149203213717)
              ·
                refine ⟨1286416465514444493900643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27443551264308149203213717 1286416465514444493900643)
                ·
                  refine ⟨1929624698271666740850965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286416465514444493900643 1929624698271666740850965)
                  ·
                    refine ⟨90451157731484378477389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1929624698271666740850965 90451157731484378477389)
                    ·
                      rfl

theorem cell23_528459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_528459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528459 prefixEnd_528459 := by exact prefixLift 528459
  have htrace : WordTrace (prefixWord ++ tailWord_528459) baseStart_528459 baseEnd_528459 := by
    simpa [prefixWord, tailWord_528459, baseEnd_528459] using wordTrace_append hprefix tailTrace_528459
  have hstable : (prefixWord ++ tailWord_528459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528459).length < 2 ^ (prefixWord ++ tailWord_528459).sum := by decide
  have hdescent : baseEnd_528459 < baseStart_528459 := by decide
  rcases family_descends (prefixWord ++ tailWord_528459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528479 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_528479 : Nat := 118140960795 + 528479 * 2 ^ 59
def prefixEnd_528479 : Nat := 4983230072969 + 3 ^ 40 * 528479 * 2
def baseEnd_528479 : Nat := 271363742807543057182075

theorem tailTrace_528479 : CollatzResearch.WordTrace tailWord_528479 prefixEnd_528479 271363742807543057182075 := by
  unfold tailWord_528479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275212652418314872580491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12850141768278876581720327 19275212652418314872580491)
  ·
    refine ⟨28912818978627472308870737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19275212652418314872580491 28912818978627472308870737)
    ·
      refine ⟨21684614233970604231653053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28912818978627472308870737 21684614233970604231653053)
      ·
        refine ⟨8131730337738976586869895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21684614233970604231653053 8131730337738976586869895)
        ·
          refine ⟨12197595506608464880304843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8131730337738976586869895 12197595506608464880304843)
          ·
            refine ⟨18296393259912697320457265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12197595506608464880304843 18296393259912697320457265)
            ·
              refine ⟨13722294944934522990342949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18296393259912697320457265 13722294944934522990342949)
              ·
                refine ⟨2572930302175223060689303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13722294944934522990342949 2572930302175223060689303)
                ·
                  refine ⟨3859395453262834591033955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572930302175223060689303 3859395453262834591033955)
                  ·
                    refine ⟨5789093179894251886550933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859395453262834591033955 5789093179894251886550933)
                    ·
                      refine ⟨271363742807543057182075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5789093179894251886550933 271363742807543057182075)
                      ·
                        rfl

theorem cell23_528479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_528479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528479 prefixEnd_528479 := by exact prefixLift 528479
  have htrace : WordTrace (prefixWord ++ tailWord_528479) baseStart_528479 baseEnd_528479 := by
    simpa [prefixWord, tailWord_528479, baseEnd_528479] using wordTrace_append hprefix tailTrace_528479
  have hstable : (prefixWord ++ tailWord_528479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528479).length < 2 ^ (prefixWord ++ tailWord_528479).sum := by decide
  have hdescent : baseEnd_528479 < baseStart_528479 := by decide
  rcases family_descends (prefixWord ++ tailWord_528479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528493 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_528493 : Nat := 118140960795 + 528493 * 2 ^ 59
def prefixEnd_528493 : Nat := 4983230072969 + 3 ^ 40 * 528493 * 2
def baseEnd_528493 : Nat := 90456977178902000802337

theorem tailTrace_528493 : CollatzResearch.WordTrace tailWord_528493 prefixEnd_528493 90456977178902000802337 := by
  unfold tailWord_528493
  simp only [CollatzResearch.WordTrace]
  refine ⟨19275723274367595263590133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12850482182911730175726755 19275723274367595263590133)
  ·
    refine ⟨1807099056971962055961575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19275723274367595263590133 1807099056971962055961575)
    ·
      refine ⟨2710648585457943083942363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807099056971962055961575 2710648585457943083942363)
      ·
        refine ⟨4065972878186914625913545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2710648585457943083942363 4065972878186914625913545)
        ·
          refine ⟨3049479658640185969435159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4065972878186914625913545 3049479658640185969435159)
          ·
            refine ⟨4574219487960278954152739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049479658640185969435159 4574219487960278954152739)
            ·
              refine ⟨6861329231940418431229109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574219487960278954152739 6861329231940418431229109)
              ·
                refine ⟨643249615494414227927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6861329231940418431229109 643249615494414227927729)
                ·
                  refine ⟨482437211620810670945797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643249615494414227927729 482437211620810670945797)
                  ·
                    refine ⟨90456977178902000802337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482437211620810670945797 90456977178902000802337)
                    ·
                      rfl

theorem cell23_528493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_528493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528493 prefixEnd_528493 := by exact prefixLift 528493
  have htrace : WordTrace (prefixWord ++ tailWord_528493) baseStart_528493 baseEnd_528493 := by
    simpa [prefixWord, tailWord_528493, baseEnd_528493] using wordTrace_append hprefix tailTrace_528493
  have hstable : (prefixWord ++ tailWord_528493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528493).length < 2 ^ (prefixWord ++ tailWord_528493).sum := by decide
  have hdescent : baseEnd_528493 < baseStart_528493 := by decide
  rcases family_descends (prefixWord ++ tailWord_528493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528496 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_528496 : Nat := 118140960795 + 528496 * 2 ^ 59
def prefixEnd_528496 : Nat := 4983230072969 + 3 ^ 40 * 528496 * 2
def baseEnd_528496 : Nat := 271372471978669490669497

theorem tailTrace_528496 : CollatzResearch.WordTrace tailWord_528496 prefixEnd_528496 271372471978669490669497 := by
  unfold tailWord_528496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637916346678363387974671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12850555128904484517299561 9637916346678363387974671)
  ·
    refine ⟨14456874520017545081962007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637916346678363387974671 14456874520017545081962007)
    ·
      refine ⟨21685311780026317622943011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456874520017545081962007 21685311780026317622943011)
      ·
        refine ⟨32527967670039476434414517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21685311780026317622943011 32527967670039476434414517)
        ·
          refine ⟨3049496969066200915726361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32527967670039476434414517 3049496969066200915726361)
          ·
            refine ⟨2287122726799650686794771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3049496969066200915726361 2287122726799650686794771)
            ·
              refine ⟨3430684090199476030192157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287122726799650686794771 3430684090199476030192157)
              ·
                refine ⟨1286506533824803511322059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3430684090199476030192157 1286506533824803511322059)
                ·
                  refine ⟨1929759800737205266983089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286506533824803511322059 1929759800737205266983089)
                  ·
                    refine ⟨1447319850552903950237317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1929759800737205266983089 1447319850552903950237317)
                    ·
                      refine ⟨271372471978669490669497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1447319850552903950237317 271372471978669490669497)
                      ·
                        rfl

theorem cell23_528496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_528496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528496 prefixEnd_528496 := by exact prefixLift 528496
  have htrace : WordTrace (prefixWord ++ tailWord_528496) baseStart_528496 baseEnd_528496 := by
    simpa [prefixWord, tailWord_528496, baseEnd_528496] using wordTrace_append hprefix tailTrace_528496
  have hstable : (prefixWord ++ tailWord_528496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528496).length < 2 ^ (prefixWord ++ tailWord_528496).sum := by decide
  have hdescent : baseEnd_528496 < baseStart_528496 := by decide
  rcases family_descends (prefixWord ++ tailWord_528496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528517 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_528517 : Nat := 118140960795 + 528517 * 2 ^ 59
def prefixEnd_528517 : Nat := 4983230072969 + 3 ^ 40 * 528517 * 2
def baseEnd_528517 : Nat := 271383255072413908506901

theorem tailTrace_528517 : CollatzResearch.WordTrace tailWord_528517 prefixEnd_528517 271383255072413908506901 := by
  unfold tailWord_528517
  simp only [CollatzResearch.WordTrace]
  refine ⟨19276598626280647362463805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12851065750853764908309203 19276598626280647362463805)
  ·
    refine ⟨7228724484855242760923927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19276598626280647362463805 7228724484855242760923927)
    ·
      refine ⟨10843086727282864141385891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228724484855242760923927 10843086727282864141385891)
      ·
        refine ⟨16264630090924296212078837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843086727282864141385891 16264630090924296212078837)
        ·
          refine ⟨1524809071024152769882391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16264630090924296212078837 1524809071024152769882391)
          ·
            refine ⟨2287213606536229154823587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524809071024152769882391 2287213606536229154823587)
            ·
              refine ⟨3430820409804343732235381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287213606536229154823587 3430820409804343732235381)
              ·
                refine ⟨321639413419157224897067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3430820409804343732235381 321639413419157224897067)
                ·
                  refine ⟨482459120128735837345601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321639413419157224897067 482459120128735837345601)
                  ·
                    refine ⟨361844340096551878009201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482459120128735837345601 361844340096551878009201)
                    ·
                      refine ⟨271383255072413908506901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361844340096551878009201 271383255072413908506901)
                      ·
                        rfl

theorem cell23_528517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_528517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528517 prefixEnd_528517 := by exact prefixLift 528517
  have htrace : WordTrace (prefixWord ++ tailWord_528517) baseStart_528517 baseEnd_528517 := by
    simpa [prefixWord, tailWord_528517, baseEnd_528517] using wordTrace_append hprefix tailTrace_528517
  have hstable : (prefixWord ++ tailWord_528517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528517).length < 2 ^ (prefixWord ++ tailWord_528517).sum := by decide
  have hdescent : baseEnd_528517 < baseStart_528517 := by decide
  rcases family_descends (prefixWord ++ tailWord_528517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528520 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_528520 : Nat := 118140960795 + 528520 * 2 ^ 59
def prefixEnd_528520 : Nat := 4983230072969 + 3 ^ 40 * 528520 * 2
def baseEnd_528520 : Nat := 271384795514377396769387

theorem tailTrace_528520 : CollatzResearch.WordTrace tailWord_528520 prefixEnd_528520 271384795514377396769387 := by
  unfold tailWord_528520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9638354022634889437411507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12851138696846519249882009 9638354022634889437411507)
  ·
    refine ⟨14457531033952334156117261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9638354022634889437411507 14457531033952334156117261)
    ·
      refine ⟨5421574137732125308543973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14457531033952334156117261 5421574137732125308543973)
      ·
        refine ⟨1016545150824773495351995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5421574137732125308543973 1016545150824773495351995)
        ·
          refine ⟨1524817726237160243027993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016545150824773495351995 1524817726237160243027993)
          ·
            refine ⟨1143613294677870182270995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1524817726237160243027993 1143613294677870182270995)
            ·
              refine ⟨1715419942016805273406493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143613294677870182270995 1715419942016805273406493)
              ·
                refine ⟨643282478256301977527435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1715419942016805273406493 643282478256301977527435)
                ·
                  refine ⟨964923717384452966291153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643282478256301977527435 964923717384452966291153)
                  ·
                    refine ⟨723692788038339724718365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964923717384452966291153 723692788038339724718365)
                    ·
                      refine ⟨271384795514377396769387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723692788038339724718365 271384795514377396769387)
                      ·
                        rfl

theorem cell23_528520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_528520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528520 prefixEnd_528520 := by exact prefixLift 528520
  have htrace : WordTrace (prefixWord ++ tailWord_528520) baseStart_528520 baseEnd_528520 := by
    simpa [prefixWord, tailWord_528520, baseEnd_528520] using wordTrace_append hprefix tailTrace_528520
  have hstable : (prefixWord ++ tailWord_528520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528520).length < 2 ^ (prefixWord ++ tailWord_528520).sum := by decide
  have hdescent : baseEnd_528520 < baseStart_528520 := by decide
  rcases family_descends (prefixWord ++ tailWord_528520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528533 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_528533 : Nat := 118140960795 + 528533 * 2 ^ 59
def prefixEnd_528533 : Nat := 4983230072969 + 3 ^ 40 * 528533 * 2
def baseEnd_528533 : Nat := 271391470762885845906827

theorem tailTrace_528533 : CollatzResearch.WordTrace tailWord_528533 prefixEnd_528533 271391470762885845906827 := by
  unfold tailWord_528533
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277182194222682095046253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12851454796148454730030835 19277182194222682095046253)
  ·
    refine ⟨7228943322833505785642345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19277182194222682095046253 7228943322833505785642345)
    ·
      refine ⟨5421707492125129339231759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7228943322833505785642345 5421707492125129339231759)
      ·
        refine ⟨8132561238187694008847639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5421707492125129339231759 8132561238187694008847639)
        ·
          refine ⟨12198841857281541013271459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132561238187694008847639 12198841857281541013271459)
          ·
            refine ⟨18298262785922311519907189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12198841857281541013271459 18298262785922311519907189)
            ·
              refine ⟨1715462136180216704991299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18298262785922311519907189 1715462136180216704991299)
              ·
                refine ⟨2573193204270325057486949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715462136180216704991299 2573193204270325057486949)
                ·
                  refine ⟨482473725800685948278803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2573193204270325057486949 482473725800685948278803)
                  ·
                    refine ⟨723710588701028922418205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482473725800685948278803 723710588701028922418205)
                    ·
                      refine ⟨271391470762885845906827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 723710588701028922418205 271391470762885845906827)
                      ·
                        rfl

theorem cell23_528533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_528533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528533 prefixEnd_528533 := by exact prefixLift 528533
  have htrace : WordTrace (prefixWord ++ tailWord_528533) baseStart_528533 baseEnd_528533 := by
    simpa [prefixWord, tailWord_528533, baseEnd_528533] using wordTrace_append hprefix tailTrace_528533
  have hstable : (prefixWord ++ tailWord_528533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528533).length < 2 ^ (prefixWord ++ tailWord_528533).sum := by decide
  have hdescent : baseEnd_528533 < baseStart_528533 := by decide
  rcases family_descends (prefixWord ++ tailWord_528533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 4, 2]
def baseStart_528573 : Nat := 118140960795 + 528573 * 2 ^ 59
def prefixEnd_528573 : Nat := 4983230072969 + 3 ^ 40 * 528573 * 2
def baseEnd_528573 : Nat := 271412009989065689406643

theorem tailTrace_528573 : CollatzResearch.WordTrace tailWord_528573 prefixEnd_528573 271412009989065689406643 := by
  unfold tailWord_528573
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278641114077768926502373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12852427409385179284334915 19278641114077768926502373)
  ·
    refine ⟨3614745208889581673719195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19278641114077768926502373 3614745208889581673719195)
    ·
      refine ⟨5422117813334372510578793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614745208889581673719195 5422117813334372510578793)
      ·
        refine ⟨4066588360000779382934095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422117813334372510578793 4066588360000779382934095)
        ·
          refine ⟨6099882540001169074401143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066588360000779382934095 6099882540001169074401143)
          ·
            refine ⟨9149823810001753611601715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099882540001169074401143 9149823810001753611601715)
            ·
              refine ⟨13724735715002630417402573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9149823810001753611601715 13724735715002630417402573)
              ·
                refine ⟨5146775893125986406525965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13724735715002630417402573 5146775893125986406525965)
                ·
                  refine ⟨1930040959922244902447237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5146775893125986406525965 1930040959922244902447237)
                  ·
                    refine ⟨361882679985420919208857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1930040959922244902447237 361882679985420919208857)
                    ·
                      refine ⟨271412009989065689406643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361882679985420919208857 271412009989065689406643)
                      ·
                        rfl

theorem cell23_528573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_528573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528573 prefixEnd_528573 := by exact prefixLift 528573
  have htrace : WordTrace (prefixWord ++ tailWord_528573) baseStart_528573 baseEnd_528573 := by
    simpa [prefixWord, tailWord_528573, baseEnd_528573] using wordTrace_append hprefix tailTrace_528573
  have hstable : (prefixWord ++ tailWord_528573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528573).length < 2 ^ (prefixWord ++ tailWord_528573).sum := by decide
  have hdescent : baseEnd_528573 < baseStart_528573 := by decide
  rcases family_descends (prefixWord ++ tailWord_528573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528576 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_528576 : Nat := 118140960795 + 528576 * 2 ^ 59
def prefixEnd_528576 : Nat := 4983230072969 + 3 ^ 40 * 528576 * 2
def baseEnd_528576 : Nat := 271413550431029177669129

theorem tailTrace_528576 : CollatzResearch.WordTrace tailWord_528576 prefixEnd_528576 271413550431029177669129 := by
  unfold tailWord_528576
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639375266533450219430791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12852500355377933625907721 9639375266533450219430791)
  ·
    refine ⟨14459062899800175329146187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9639375266533450219430791 14459062899800175329146187)
    ·
      refine ⟨21688594349700262993719281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459062899800175329146187 21688594349700262993719281)
      ·
        refine ⟨16266445762275197245289461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21688594349700262993719281 16266445762275197245289461)
        ·
          refine ⟨1524979290213299741745887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16266445762275197245289461 1524979290213299741745887)
          ·
            refine ⟨2287468935319949612618831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524979290213299741745887 2287468935319949612618831)
            ·
              refine ⟨3431203402979924418928247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287468935319949612618831 3431203402979924418928247)
              ·
                refine ⟨5146805104469886628392371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431203402979924418928247 5146805104469886628392371)
                ·
                  refine ⟨7720207656704829942588557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146805104469886628392371 7720207656704829942588557)
                  ·
                    refine ⟨2895077871264311228470709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7720207656704829942588557 2895077871264311228470709)
                    ·
                      refine ⟨271413550431029177669129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2895077871264311228470709 271413550431029177669129)
                      ·
                        rfl

theorem cell23_528576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_528576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528576 prefixEnd_528576 := by exact prefixLift 528576
  have htrace : WordTrace (prefixWord ++ tailWord_528576) baseStart_528576 baseEnd_528576 := by
    simpa [prefixWord, tailWord_528576, baseEnd_528576] using wordTrace_append hprefix tailTrace_528576
  have hstable : (prefixWord ++ tailWord_528576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528576).length < 2 ^ (prefixWord ++ tailWord_528576).sum := by decide
  have hdescent : baseEnd_528576 < baseStart_528576 := by decide
  rcases family_descends (prefixWord ++ tailWord_528576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528611 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 1, 3, 2]
def baseStart_528611 : Nat := 118140960795 + 528611 * 2 ^ 59
def prefixEnd_528611 : Nat := 4983230072969 + 3 ^ 40 * 528611 * 2
def baseEnd_528611 : Nat := 271431522253936540731469

theorem tailTrace_528611 : CollatzResearch.WordTrace tailWord_528611 prefixEnd_528611 271431522253936540731469 := by
  unfold tailWord_528611
  simp only [CollatzResearch.WordTrace]
  refine ⟨19280027087940101416385687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12853351391960067610923791 19280027087940101416385687)
  ·
    refine ⟨28920040631910152124578531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19280027087940101416385687 28920040631910152124578531)
    ·
      refine ⟨43380060947865228186867797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28920040631910152124578531 43380060947865228186867797)
      ·
        refine ⟨508360089232795642814857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 43380060947865228186867797 508360089232795642814857)
        ·
          refine ⟨381270066924596732111143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508360089232795642814857 381270066924596732111143)
          ·
            refine ⟨571905100386895098166715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381270066924596732111143 571905100386895098166715)
            ·
              refine ⟨857857650580342647250073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571905100386895098166715 857857650580342647250073)
              ·
                refine ⟨643393237935256985437555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857857650580342647250073 643393237935256985437555)
                ·
                  refine ⟨965089856902885478156333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643393237935256985437555 965089856902885478156333)
                  ·
                    refine ⟨361908696338582054308625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965089856902885478156333 361908696338582054308625)
                    ·
                      refine ⟨271431522253936540731469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361908696338582054308625 271431522253936540731469)
                      ·
                        rfl

theorem cell23_528611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_528611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528611 prefixEnd_528611 := by exact prefixLift 528611
  have htrace : WordTrace (prefixWord ++ tailWord_528611) baseStart_528611 baseEnd_528611 := by
    simpa [prefixWord, tailWord_528611, baseEnd_528611] using wordTrace_append hprefix tailTrace_528611
  have hstable : (prefixWord ++ tailWord_528611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528611).length < 2 ^ (prefixWord ++ tailWord_528611).sum := by decide
  have hdescent : baseEnd_528611 < baseStart_528611 := by decide
  rcases family_descends (prefixWord ++ tailWord_528611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528647 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 5]
def baseStart_528647 : Nat := 118140960795 + 528647 * 2 ^ 59
def prefixEnd_528647 : Nat := 4983230072969 + 3 ^ 40 * 528647 * 2
def baseEnd_528647 : Nat := 30161111950833155542367

theorem tailTrace_528647 : CollatzResearch.WordTrace tailWord_528647 prefixEnd_528647 30161111950833155542367 := by
  unfold tailWord_528647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19281340115809679564696195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854226743873119709797463 19281340115809679564696195)
  ·
    refine ⟨28922010173714519347044293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19281340115809679564696195 28922010173714519347044293)
    ·
      refine ⟨5422876907571472377570805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28922010173714519347044293 5422876907571472377570805)
      ·
        refine ⟨508394710084825535397263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5422876907571472377570805 508394710084825535397263)
        ·
          refine ⟨762592065127238303095895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508394710084825535397263 762592065127238303095895)
          ·
            refine ⟨1143888097690857454643843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762592065127238303095895 1143888097690857454643843)
            ·
              refine ⟨1715832146536286181965765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143888097690857454643843 1715832146536286181965765)
              ·
                refine ⟨321718527475553659118581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1715832146536286181965765 321718527475553659118581)
                ·
                  refine ⟨30161111950833155542367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321718527475553659118581 30161111950833155542367)
                  ·
                    rfl

theorem cell23_528647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 5].length) (baseStart_528647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528647 prefixEnd_528647 := by exact prefixLift 528647
  have htrace : WordTrace (prefixWord ++ tailWord_528647) baseStart_528647 baseEnd_528647 := by
    simpa [prefixWord, tailWord_528647, baseEnd_528647] using wordTrace_append hprefix tailTrace_528647
  have hstable : (prefixWord ++ tailWord_528647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528647).length < 2 ^ (prefixWord ++ tailWord_528647).sum := by decide
  have hdescent : baseEnd_528647 < baseStart_528647 := by decide
  rcases family_descends (prefixWord ++ tailWord_528647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528673 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_528673 : Nat := 118140960795 + 528673 * 2 ^ 59
def prefixEnd_528673 : Nat := 4983230072969 + 3 ^ 40 * 528673 * 2
def baseEnd_528673 : Nat := 90487786018171766052061

theorem tailTrace_528673 : CollatzResearch.WordTrace tailWord_528673 prefixEnd_528673 90487786018171766052061 := by
  unfold tailWord_528673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282288413715486005142673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854858942476990670095115 19282288413715486005142673)
  ·
    refine ⟨14461716310286614503857005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19282288413715486005142673 14461716310286614503857005)
    ·
      refine ⟨5423143616357480438946377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14461716310286614503857005 5423143616357480438946377)
      ·
        refine ⟨4067357712268110329209783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5423143616357480438946377 4067357712268110329209783)
        ·
          refine ⟨6101036568402165493814675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067357712268110329209783 6101036568402165493814675)
          ·
            refine ⟨9151554852603248240722013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101036568402165493814675 9151554852603248240722013)
            ·
              refine ⟨3431833069726218090270755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9151554852603248240722013 3431833069726218090270755)
              ·
                refine ⟨5147749604589327135406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431833069726218090270755 5147749604589327135406133)
                ·
                  refine ⟨482601525430249418944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5147749604589327135406133 482601525430249418944325)
                  ·
                    refine ⟨90487786018171766052061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482601525430249418944325 90487786018171766052061)
                    ·
                      rfl

theorem cell23_528673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_528673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528673 prefixEnd_528673 := by exact prefixLift 528673
  have htrace : WordTrace (prefixWord ++ tailWord_528673) baseStart_528673 baseEnd_528673 := by
    simpa [prefixWord, tailWord_528673, baseEnd_528673] using wordTrace_append hprefix tailTrace_528673
  have hstable : (prefixWord ++ tailWord_528673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528673).length < 2 ^ (prefixWord ++ tailWord_528673).sum := by decide
  have hdescent : baseEnd_528673 < baseStart_528673 := by decide
  rcases family_descends (prefixWord ++ tailWord_528673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528677 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 2, 5]
def baseStart_528677 : Nat := 118140960795 + 528677 * 2 ^ 59
def prefixEnd_528677 : Nat := 4983230072969 + 3 ^ 40 * 528677 * 2
def baseEnd_528677 : Nat := 90488470659044427502055

theorem tailTrace_528677 : CollatzResearch.WordTrace tailWord_528677 prefixEnd_528677 90488470659044427502055 := by
  unfold tailWord_528677
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282434305700994688288285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12854956203800663125525523 19282434305700994688288285)
  ·
    refine ⟨7230912864637873008108107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19282434305700994688288285 7230912864637873008108107)
    ·
      refine ⟨10846369296956809512162161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230912864637873008108107 10846369296956809512162161)
      ·
        refine ⟨8134776972717607134121621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10846369296956809512162161 8134776972717607134121621)
        ·
          refine ⟨381317670596137834411951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8134776972717607134121621 381317670596137834411951)
          ·
            refine ⟨571976505894206751617927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381317670596137834411951 571976505894206751617927)
            ·
              refine ⟨857964758841310127426891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571976505894206751617927 857964758841310127426891)
              ·
                refine ⟨1286947138261965191140337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857964758841310127426891 1286947138261965191140337)
                ·
                  refine ⟨965210353696473893355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286947138261965191140337 965210353696473893355253)
                  ·
                    refine ⟨90488470659044427502055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 965210353696473893355253 90488470659044427502055)
                    ·
                      rfl

theorem cell23_528677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_528677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528677 prefixEnd_528677 := by exact prefixLift 528677
  have htrace : WordTrace (prefixWord ++ tailWord_528677) baseStart_528677 baseEnd_528677 := by
    simpa [prefixWord, tailWord_528677, baseEnd_528677] using wordTrace_append hprefix tailTrace_528677
  have hstable : (prefixWord ++ tailWord_528677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528677).length < 2 ^ (prefixWord ++ tailWord_528677).sum := by decide
  have hdescent : baseEnd_528677 < baseStart_528677 := by decide
  rcases family_descends (prefixWord ++ tailWord_528677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528680 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_528680 : Nat := 118140960795 + 528680 * 2 ^ 59
def prefixEnd_528680 : Nat := 4983230072969 + 3 ^ 40 * 528680 * 2
def baseEnd_528680 : Nat := 271466952419096770768651

theorem tailTrace_528680 : CollatzResearch.WordTrace tailWord_528680 prefixEnd_528680 271466952419096770768651 := by
  unfold tailWord_528680
  simp only [CollatzResearch.WordTrace]
  refine ⟨9641271862345063100323747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12855029149793417467098329 9641271862345063100323747)
  ·
    refine ⟨14461907793517594650485621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9641271862345063100323747 14461907793517594650485621)
    ·
      refine ⟨1355803855642274498483027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14461907793517594650485621 1355803855642274498483027)
      ·
        refine ⟨2033705783463411747724541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355803855642274498483027 2033705783463411747724541)
        ·
          refine ⟨762639668798779405396703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2033705783463411747724541 762639668798779405396703)
          ·
            refine ⟨1143959503198169108095055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762639668798779405396703 1143959503198169108095055)
            ·
              refine ⟨1715939254797253662142583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143959503198169108095055 1715939254797253662142583)
              ·
                refine ⟨2573908882195880493213875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715939254797253662142583 2573908882195880493213875)
                ·
                  refine ⟨3860863323293820739820813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573908882195880493213875 3860863323293820739820813)
                  ·
                    refine ⟨1447823746235182777432805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3860863323293820739820813 1447823746235182777432805)
                    ·
                      refine ⟨271466952419096770768651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1447823746235182777432805 271466952419096770768651)
                      ·
                        rfl

theorem cell23_528680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_528680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528680 prefixEnd_528680 := by exact prefixLift 528680
  have htrace : WordTrace (prefixWord ++ tailWord_528680) baseStart_528680 baseEnd_528680 := by
    simpa [prefixWord, tailWord_528680, baseEnd_528680] using wordTrace_append hprefix tailTrace_528680
  have hstable : (prefixWord ++ tailWord_528680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528680).length < 2 ^ (prefixWord ++ tailWord_528680).sum := by decide
  have hdescent : baseEnd_528680 < baseStart_528680 := by decide
  rcases family_descends (prefixWord ++ tailWord_528680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528720 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 6]
def baseStart_528720 : Nat := 118140960795 + 528720 * 2 ^ 59
def prefixEnd_528720 : Nat := 4983230072969 + 3 ^ 40 * 528720 * 2
def baseEnd_528720 : Nat := 30165276849475179363163

theorem tailTrace_528720 : CollatzResearch.WordTrace tailWord_528720 prefixEnd_528720 30165276849475179363163 := by
  unfold tailWord_528720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642001322272606516051807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12856001763030142021402409 9642001322272606516051807)
  ·
    refine ⟨14463001983408909774077711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9642001322272606516051807 14463001983408909774077711)
    ·
      refine ⟨21694502975113364661116567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14463001983408909774077711 21694502975113364661116567)
      ·
        refine ⟨32541754462670046991674851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21694502975113364661116567 32541754462670046991674851)
        ·
          refine ⟨48812631694005070487512277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32541754462670046991674851 48812631694005070487512277)
          ·
            refine ⟨1144046055328243839551069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 48812631694005070487512277 1144046055328243839551069)
            ·
              refine ⟨429017270748091439831651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144046055328243839551069 429017270748091439831651)
              ·
                refine ⟨643525906122137159747477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429017270748091439831651 643525906122137159747477)
                ·
                  refine ⟨30165276849475179363163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 643525906122137159747477 30165276849475179363163)
                  ·
                    rfl

theorem cell23_528720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_528720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528720 prefixEnd_528720 := by exact prefixLift 528720
  have htrace : WordTrace (prefixWord ++ tailWord_528720) baseStart_528720 baseEnd_528720 := by
    simpa [prefixWord, tailWord_528720, baseEnd_528720] using wordTrace_append hprefix tailTrace_528720
  have hstable : (prefixWord ++ tailWord_528720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528720).length < 2 ^ (prefixWord ++ tailWord_528720).sum := by decide
  have hdescent : baseEnd_528720 < baseStart_528720 := by decide
  rcases family_descends (prefixWord ++ tailWord_528720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528740 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_528740 : Nat := 118140960795 + 528740 * 2 ^ 59
def prefixEnd_528740 : Nat := 4983230072969 + 3 ^ 40 * 528740 * 2
def baseEnd_528740 : Nat := 271497761258366536018375

theorem tailTrace_528740 : CollatzResearch.WordTrace tailWord_528740 prefixEnd_528740 271497761258366536018375 := by
  unfold tailWord_528740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642366052236378223915837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12856488069648504298554449 9642366052236378223915837)
  ·
    refine ⟨3615887269588641833968439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9642366052236378223915837 3615887269588641833968439)
    ·
      refine ⟨5423830904382962750952659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3615887269588641833968439 5423830904382962750952659)
      ·
        refine ⟨8135746356574444126428989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5423830904382962750952659 8135746356574444126428989)
        ·
          refine ⟨3050904883715416547410871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8135746356574444126428989 3050904883715416547410871)
          ·
            refine ⟨4576357325573124821116307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050904883715416547410871 4576357325573124821116307)
            ·
              refine ⟨6864535988359687231674461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576357325573124821116307 6864535988359687231674461)
              ·
                refine ⟨2574200995634882711877923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6864535988359687231674461 2574200995634882711877923)
                ·
                  refine ⟨3861301493452324067816885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574200995634882711877923 3861301493452324067816885)
                  ·
                    refine ⟨361997015011155381357833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3861301493452324067816885 361997015011155381357833)
                    ·
                      refine ⟨271497761258366536018375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 361997015011155381357833 271497761258366536018375)
                      ·
                        rfl

theorem cell23_528740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_528740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528740 prefixEnd_528740 := by exact prefixLift 528740
  have htrace : WordTrace (prefixWord ++ tailWord_528740) baseStart_528740 baseEnd_528740 := by
    simpa [prefixWord, tailWord_528740, baseEnd_528740] using wordTrace_append hprefix tailTrace_528740
  have hstable : (prefixWord ++ tailWord_528740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528740).length < 2 ^ (prefixWord ++ tailWord_528740).sum := by decide
  have hdescent : baseEnd_528740 < baseStart_528740 := by decide
  rcases family_descends (prefixWord ++ tailWord_528740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528753 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_528753 : Nat := 118140960795 + 528753 * 2 ^ 59
def prefixEnd_528753 : Nat := 4983230072969 + 3 ^ 40 * 528753 * 2
def baseEnd_528753 : Nat := 271504436506874985155815

theorem tailTrace_528753 : CollatzResearch.WordTrace tailWord_528753 prefixEnd_528753 271504436506874985155815 := by
  unfold tailWord_528753
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285206253425659668054913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12856804168950439778703275 19285206253425659668054913)
  ·
    refine ⟨14463904690069244751041185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19285206253425659668054913 14463904690069244751041185)
    ·
      refine ⟨10847928517551933563280889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14463904690069244751041185 10847928517551933563280889)
      ·
        refine ⟨8135946388163950172460667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10847928517551933563280889 8135946388163950172460667)
        ·
          refine ⟨12203919582245925258691001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8135946388163950172460667 12203919582245925258691001)
          ·
            refine ⟨9152939686684443944018251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12203919582245925258691001 9152939686684443944018251)
            ·
              refine ⟨13729409530026665916027377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152939686684443944018251 13729409530026665916027377)
              ·
                refine ⟨10297057147519999437020533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13729409530026665916027377 10297057147519999437020533)
                ·
                  refine ⟨965349107579999947220675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10297057147519999437020533 965349107579999947220675)
                  ·
                    refine ⟨1448023661369999920831013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 965349107579999947220675 1448023661369999920831013)
                    ·
                      refine ⟨271504436506874985155815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1448023661369999920831013 271504436506874985155815)
                      ·
                        rfl

theorem cell23_528753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_528753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528753 prefixEnd_528753 := by exact prefixLift 528753
  have htrace : WordTrace (prefixWord ++ tailWord_528753) baseStart_528753 baseEnd_528753 := by
    simpa [prefixWord, tailWord_528753, baseEnd_528753] using wordTrace_append hprefix tailTrace_528753
  have hstable : (prefixWord ++ tailWord_528753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528753).length < 2 ^ (prefixWord ++ tailWord_528753).sum := by decide
  have hdescent : baseEnd_528753 < baseStart_528753 := by decide
  rcases family_descends (prefixWord ++ tailWord_528753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528757 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_528757 : Nat := 118140960795 + 528757 * 2 ^ 59
def prefixEnd_528757 : Nat := 4983230072969 + 3 ^ 40 * 528757 * 2
def baseEnd_528757 : Nat := 271506490429492969505797

theorem tailTrace_528757 : CollatzResearch.WordTrace tailWord_528757 prefixEnd_528757 271506490429492969505797 := by
  unfold tailWord_528757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285352145411168351200525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12856901430274112234133683 19285352145411168351200525)
  ·
    refine ⟨7232007054529188131700197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19285352145411168351200525 7232007054529188131700197)
    ·
      refine ⟨1356001322724222774693787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7232007054529188131700197 1356001322724222774693787)
      ·
        refine ⟨2034001984086334162040681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356001322724222774693787 2034001984086334162040681)
        ·
          refine ⟨1525501488064750621530511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2034001984086334162040681 1525501488064750621530511)
          ·
            refine ⟨2288252232097125932295767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525501488064750621530511 2288252232097125932295767)
            ·
              refine ⟨3432378348145688898443651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288252232097125932295767 3432378348145688898443651)
              ·
                refine ⟨5148567522218533347665477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432378348145688898443651 5148567522218533347665477)
                ·
                  refine ⟨965356410415975002687277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5148567522218533347665477 965356410415975002687277)
                  ·
                    refine ⟨362008653905990626007729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965356410415975002687277 362008653905990626007729)
                    ·
                      refine ⟨271506490429492969505797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362008653905990626007729 271506490429492969505797)
                      ·
                        rfl

theorem cell23_528757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_528757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528757 prefixEnd_528757 := by exact prefixLift 528757
  have htrace : WordTrace (prefixWord ++ tailWord_528757) baseStart_528757 baseEnd_528757 := by
    simpa [prefixWord, tailWord_528757, baseEnd_528757] using wordTrace_append hprefix tailTrace_528757
  have hstable : (prefixWord ++ tailWord_528757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528757).length < 2 ^ (prefixWord ++ tailWord_528757).sum := by decide
  have hdescent : baseEnd_528757 < baseStart_528757 := by decide
  rcases family_descends (prefixWord ++ tailWord_528757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528758 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_528758 : Nat := 118140960795 + 528758 * 2 ^ 59
def prefixEnd_528758 : Nat := 4983230072969 + 3 ^ 40 * 528758 * 2
def baseEnd_528758 : Nat := 90502334636715821864431

theorem tailTrace_528758 : CollatzResearch.WordTrace tailWord_528758 prefixEnd_528758 90502334636715821864431 := by
  unfold tailWord_528758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205336788650471595124183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12856925745605030347991285 1205336788650471595124183)
  ·
    refine ⟨1808005182975707392686275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205336788650471595124183 1808005182975707392686275)
    ·
      refine ⟨2712007774463561089029413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808005182975707392686275 2712007774463561089029413)
      ·
        refine ⟨508501457711917704193015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2712007774463561089029413 508501457711917704193015)
        ·
          refine ⟨762752186567876556289523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508501457711917704193015 762752186567876556289523)
          ·
            refine ⟨1144128279851814834434285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762752186567876556289523 1144128279851814834434285)
            ·
              refine ⟨429048104944430562912857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144128279851814834434285 429048104944430562912857)
              ·
                refine ⟨321786078708322922184643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429048104944430562912857 321786078708322922184643)
                ·
                  refine ⟨482679118062484383276965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321786078708322922184643 482679118062484383276965)
                  ·
                    refine ⟨90502334636715821864431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 482679118062484383276965 90502334636715821864431)
                    ·
                      rfl

theorem cell23_528758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_528758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528758 prefixEnd_528758 := by exact prefixLift 528758
  have htrace : WordTrace (prefixWord ++ tailWord_528758) baseStart_528758 baseEnd_528758 := by
    simpa [prefixWord, tailWord_528758, baseEnd_528758] using wordTrace_append hprefix tailTrace_528758
  have hstable : (prefixWord ++ tailWord_528758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528758).length < 2 ^ (prefixWord ++ tailWord_528758).sum := by decide
  have hdescent : baseEnd_528758 < baseStart_528758 := by decide
  rcases family_descends (prefixWord ++ tailWord_528758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528773 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_528773 : Nat := 118140960795 + 528773 * 2 ^ 59
def prefixEnd_528773 : Nat := 4983230072969 + 3 ^ 40 * 528773 * 2
def baseEnd_528773 : Nat := 271514706119964906905723

theorem tailTrace_528773 : CollatzResearch.WordTrace tailWord_528773 prefixEnd_528773 271514706119964906905723 := by
  unfold tailWord_528773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19285935713353203083782973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12857290475568802055855315 19285935713353203083782973)
  ·
    refine ⟨7232225892507451156418615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19285935713353203083782973 7232225892507451156418615)
    ·
      refine ⟨10848338838761176734627923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232225892507451156418615 10848338838761176734627923)
      ·
        refine ⟨16272508258141765101941885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848338838761176734627923 16272508258141765101941885)
        ·
          refine ⟨6102190596803161913228207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16272508258141765101941885 6102190596803161913228207)
          ·
            refine ⟨9153285895204742869842311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102190596803161913228207 9153285895204742869842311)
            ·
              refine ⟨13729928842807114304763467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9153285895204742869842311 13729928842807114304763467)
              ·
                refine ⟨20594893264210671457145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13729928842807114304763467 20594893264210671457145201)
                ·
                  refine ⟨15446169948158003592858901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20594893264210671457145201 15446169948158003592858901)
                  ·
                    refine ⟨724039216319906418415261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15446169948158003592858901 724039216319906418415261)
                    ·
                      refine ⟨271514706119964906905723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724039216319906418415261 271514706119964906905723)
                      ·
                        rfl

theorem cell23_528773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_528773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528773 prefixEnd_528773 := by exact prefixLift 528773
  have htrace : WordTrace (prefixWord ++ tailWord_528773) baseStart_528773 baseEnd_528773 := by
    simpa [prefixWord, tailWord_528773, baseEnd_528773] using wordTrace_append hprefix tailTrace_528773
  have hstable : (prefixWord ++ tailWord_528773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528773).length < 2 ^ (prefixWord ++ tailWord_528773).sum := by decide
  have hdescent : baseEnd_528773 < baseStart_528773 := by decide
  rcases family_descends (prefixWord ++ tailWord_528773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528800 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_528800 : Nat := 118140960795 + 528800 * 2 ^ 59
def prefixEnd_528800 : Nat := 4983230072969 + 3 ^ 40 * 528800 * 2
def baseEnd_528800 : Nat := 271528570097636301268099

theorem tailTrace_528800 : CollatzResearch.WordTrace tailWord_528800 prefixEnd_528800 271528570097636301268099 := by
  unfold tailWord_528800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643460242127693347507927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12857946989503591130010569 9643460242127693347507927)
  ·
    refine ⟨14465190363191540021261891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9643460242127693347507927 14465190363191540021261891)
    ·
      refine ⟨21697785544787310031892837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14465190363191540021261891 21697785544787310031892837)
      ·
        refine ⟨4068334789647620630979907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21697785544787310031892837 4068334789647620630979907)
        ·
          refine ⟨6102502184471430946469861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4068334789647620630979907 6102502184471430946469861)
          ·
            refine ⟨1144219159588393302463099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6102502184471430946469861 1144219159588393302463099)
            ·
              refine ⟨1716328739382589953694649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144219159588393302463099 1716328739382589953694649)
              ·
                refine ⟨1287246554536942465270987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716328739382589953694649 1287246554536942465270987)
                ·
                  refine ⟨1930869831805413697906481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287246554536942465270987 1930869831805413697906481)
                  ·
                    refine ⟨1448152373854060273429861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1930869831805413697906481 1448152373854060273429861)
                    ·
                      refine ⟨271528570097636301268099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1448152373854060273429861 271528570097636301268099)
                      ·
                        rfl

theorem cell23_528800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_528800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528800 prefixEnd_528800 := by exact prefixLift 528800
  have htrace : WordTrace (prefixWord ++ tailWord_528800) baseStart_528800 baseEnd_528800 := by
    simpa [prefixWord, tailWord_528800, baseEnd_528800] using wordTrace_append hprefix tailTrace_528800
  have hstable : (prefixWord ++ tailWord_528800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528800).length < 2 ^ (prefixWord ++ tailWord_528800).sum := by decide
  have hdescent : baseEnd_528800 < baseStart_528800 := by decide
  rcases family_descends (prefixWord ++ tailWord_528800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528807 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_528807 : Nat := 118140960795 + 528807 * 2 ^ 59
def prefixEnd_528807 : Nat := 4983230072969 + 3 ^ 40 * 528807 * 2
def baseEnd_528807 : Nat := 271532164462217773880567

theorem tailTrace_528807 : CollatzResearch.WordTrace tailWord_528807 prefixEnd_528807 271532164462217773880567 := by
  unfold tailWord_528807
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287175795230026890520675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858117196820017927013783 19287175795230026890520675)
  ·
    refine ⟨28930763692845040335781013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19287175795230026890520675 28930763692845040335781013)
    ·
      refine ⟨1356129548102111265739735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28930763692845040335781013 1356129548102111265739735)
      ·
        refine ⟨2034194322153166898609603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356129548102111265739735 2034194322153166898609603)
        ·
          refine ⟨3051291483229750347914405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034194322153166898609603 3051291483229750347914405)
          ·
            refine ⟨572117153105578190233951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3051291483229750347914405 572117153105578190233951)
            ·
              refine ⟨858175729658367285350927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572117153105578190233951 858175729658367285350927)
              ·
                refine ⟨1287263594487550928026391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858175729658367285350927 1287263594487550928026391)
                ·
                  refine ⟨1930895391731326392039587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1287263594487550928026391 1930895391731326392039587)
                  ·
                    refine ⟨2896343087596989588059381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1930895391731326392039587 2896343087596989588059381)
                    ·
                      refine ⟨271532164462217773880567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2896343087596989588059381 271532164462217773880567)
                      ·
                        rfl

theorem cell23_528807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_528807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528807 prefixEnd_528807 := by exact prefixLift 528807
  have htrace : WordTrace (prefixWord ++ tailWord_528807) baseStart_528807 baseEnd_528807 := by
    simpa [prefixWord, tailWord_528807, baseEnd_528807] using wordTrace_append hprefix tailTrace_528807
  have hstable : (prefixWord ++ tailWord_528807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528807).length < 2 ^ (prefixWord ++ tailWord_528807).sum := by decide
  have hdescent : baseEnd_528807 < baseStart_528807 := by decide
  rcases family_descends (prefixWord ++ tailWord_528807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528823 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 7]
def baseStart_528823 : Nat := 118140960795 + 528823 * 2 ^ 59
def prefixEnd_528823 : Nat := 4983230072969 + 3 ^ 40 * 528823 * 2
def baseEnd_528823 : Nat := 90513460050896570426831

theorem tailTrace_528823 : CollatzResearch.WordTrace tailWord_528823 prefixEnd_528823 90513460050896570426831 := by
  unfold tailWord_528823
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287759363172061623103123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858506242114707748735415 19287759363172061623103123)
  ·
    refine ⟨28931639044758092434654685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19287759363172061623103123 28931639044758092434654685)
    ·
      refine ⟨10849364641784284662995507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28931639044758092434654685 10849364641784284662995507)
      ·
        refine ⟨16274046962676426994493261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849364641784284662995507 16274046962676426994493261)
        ·
          refine ⟨6102767611003660122934973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16274046962676426994493261 6102767611003660122934973)
          ·
            refine ⟨2288537854126372546100615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6102767611003660122934973 2288537854126372546100615)
            ·
              refine ⟨3432806781189558819150923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288537854126372546100615 3432806781189558819150923)
              ·
                refine ⟨5149210171784338228726385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432806781189558819150923 5149210171784338228726385)
                ·
                  refine ⟨3861907628838253671544789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149210171784338228726385 3861907628838253671544789)
                  ·
                    refine ⟨90513460050896570426831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3861907628838253671544789 90513460050896570426831)
                    ·
                      rfl

theorem cell23_528823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_528823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528823 prefixEnd_528823 := by exact prefixLift 528823
  have htrace : WordTrace (prefixWord ++ tailWord_528823) baseStart_528823 baseEnd_528823 := by
    simpa [prefixWord, tailWord_528823, baseEnd_528823] using wordTrace_append hprefix tailTrace_528823
  have hstable : (prefixWord ++ tailWord_528823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528823).length < 2 ^ (prefixWord ++ tailWord_528823).sum := by decide
  have hdescent : baseEnd_528823 < baseStart_528823 := by decide
  rcases family_descends (prefixWord ++ tailWord_528823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528843 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_528843 : Nat := 118140960795 + 528843 * 2 ^ 59
def prefixEnd_528843 : Nat := 4983230072969 + 3 ^ 40 * 528843 * 2
def baseEnd_528843 : Nat := 271550649765779633030401

theorem tailTrace_528843 : CollatzResearch.WordTrace tailWord_528843 prefixEnd_528843 271550649765779633030401 := by
  unfold tailWord_528843
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288488823099605038831183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12858992548733070025887455 19288488823099605038831183)
  ·
    refine ⟨28932733234649407558246775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19288488823099605038831183 28932733234649407558246775)
    ·
      refine ⟨43399099851974111337370163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28932733234649407558246775 43399099851974111337370163)
      ·
        refine ⟨65098649777961167006055245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43399099851974111337370163 65098649777961167006055245)
        ·
          refine ⟨24411993666735437627270717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65098649777961167006055245 24411993666735437627270717)
          ·
            refine ⟨9154497625025789110226519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24411993666735437627270717 9154497625025789110226519)
            ·
              refine ⟨13731746437538683665339779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9154497625025789110226519 13731746437538683665339779)
              ·
                refine ⟨20597619656308025498009669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13731746437538683665339779 20597619656308025498009669)
                ·
                  refine ⟨3862053685557754780876813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20597619656308025498009669 3862053685557754780876813)
                  ·
                    refine ⟨1448270132084158042828805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3862053685557754780876813 1448270132084158042828805)
                    ·
                      refine ⟨271550649765779633030401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1448270132084158042828805 271550649765779633030401)
                      ·
                        rfl

theorem cell23_528843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_528843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528843 prefixEnd_528843 := by exact prefixLift 528843
  have htrace : WordTrace (prefixWord ++ tailWord_528843) baseStart_528843 baseEnd_528843 := by
    simpa [prefixWord, tailWord_528843, baseEnd_528843] using wordTrace_append hprefix tailTrace_528843
  have hstable : (prefixWord ++ tailWord_528843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528843).length < 2 ^ (prefixWord ++ tailWord_528843).sum := by decide
  have hdescent : baseEnd_528843 < baseStart_528843 := by decide
  rcases family_descends (prefixWord ++ tailWord_528843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528847 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 1, 3, 2]
def baseStart_528847 : Nat := 118140960795 + 528847 * 2 ^ 59
def prefixEnd_528847 : Nat := 4983230072969 + 3 ^ 40 * 528847 * 2
def baseEnd_528847 : Nat := 271552703688397617380383

theorem tailTrace_528847 : CollatzResearch.WordTrace tailWord_528847 prefixEnd_528847 271552703688397617380383 := by
  unfold tailWord_528847
  simp only [CollatzResearch.WordTrace]
  refine ⟨19288634715085113721976795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12859089810056742481317863 19288634715085113721976795)
  ·
    refine ⟨28932952072627670582965193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19288634715085113721976795 28932952072627670582965193)
    ·
      refine ⟨21699714054470752937223895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28932952072627670582965193 21699714054470752937223895)
      ·
        refine ⟨32549571081706129405835843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21699714054470752937223895 32549571081706129405835843)
        ·
          refine ⟨48824356622559194108753765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32549571081706129405835843 48824356622559194108753765)
          ·
            refine ⟨9154566866729848895391331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48824356622559194108753765 9154566866729848895391331)
            ·
              refine ⟨13731850300094773343086997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9154566866729848895391331 13731850300094773343086997)
              ·
                refine ⟨643680482816942500457203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13731850300094773343086997 643680482816942500457203)
                ·
                  refine ⟨965520724225413750685805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643680482816942500457203 965520724225413750685805)
                  ·
                    refine ⟨362070271584530156507177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965520724225413750685805 362070271584530156507177)
                    ·
                      refine ⟨271552703688397617380383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362070271584530156507177 271552703688397617380383)
                      ·
                        rfl

theorem cell23_528847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3, 2].length) (baseStart_528847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528847 prefixEnd_528847 := by exact prefixLift 528847
  have htrace : WordTrace (prefixWord ++ tailWord_528847) baseStart_528847 baseEnd_528847 := by
    simpa [prefixWord, tailWord_528847, baseEnd_528847] using wordTrace_append hprefix tailTrace_528847
  have hstable : (prefixWord ++ tailWord_528847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528847).length < 2 ^ (prefixWord ++ tailWord_528847).sum := by decide
  have hdescent : baseEnd_528847 < baseStart_528847 := by decide
  rcases family_descends (prefixWord ++ tailWord_528847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528854 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_528854 : Nat := 118140960795 + 528854 * 2 ^ 59
def prefixEnd_528854 : Nat := 4983230072969 + 3 ^ 40 * 528854 * 2
def baseEnd_528854 : Nat := 271556298052979089992851

theorem tailTrace_528854 : CollatzResearch.WordTrace tailWord_528854 prefixEnd_528854 271556298052979089992851 := by
  unfold tailWord_528854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205555626628734619842601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12859260017373169278321077 1205555626628734619842601)
  ·
    refine ⟨904166719971550964881951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1205555626628734619842601 904166719971550964881951)
    ·
      refine ⟨1356250079957326447322927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904166719971550964881951 1356250079957326447322927)
      ·
        refine ⟨2034375119935989670984391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356250079957326447322927 2034375119935989670984391)
        ·
          refine ⟨3051562679903984506476587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034375119935989670984391 3051562679903984506476587)
          ·
            refine ⟨4577344019855976759714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051562679903984506476587 4577344019855976759714881)
            ·
              refine ⟨3433008014891982569786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4577344019855976759714881 3433008014891982569786161)
              ·
                refine ⟨2574756011168986927339621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433008014891982569786161 2574756011168986927339621)
                ·
                  refine ⟨482766752094185048876179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2574756011168986927339621 482766752094185048876179)
                  ·
                    refine ⟨724150128141277573314269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482766752094185048876179 724150128141277573314269)
                    ·
                      refine ⟨271556298052979089992851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724150128141277573314269 271556298052979089992851)
                      ·
                        rfl

theorem cell23_528854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_528854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528854 prefixEnd_528854 := by exact prefixLift 528854
  have htrace : WordTrace (prefixWord ++ tailWord_528854) baseStart_528854 baseEnd_528854 := by
    simpa [prefixWord, tailWord_528854, baseEnd_528854] using wordTrace_append hprefix tailTrace_528854
  have hstable : (prefixWord ++ tailWord_528854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528854).length < 2 ^ (prefixWord ++ tailWord_528854).sum := by decide
  have hdescent : baseEnd_528854 < baseStart_528854 := by decide
  rcases family_descends (prefixWord ++ tailWord_528854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528898 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_528898 : Nat := 118140960795 + 528898 * 2 ^ 59
def prefixEnd_528898 : Nat := 4983230072969 + 3 ^ 40 * 528898 * 2
def baseEnd_528898 : Nat := 271578891201776917842649

theorem tailTrace_528898 : CollatzResearch.WordTrace tailWord_528898 prefixEnd_528898 271578891201776917842649 := by
  unfold tailWord_528898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822623709475087358020837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12860329891933566288055565 4822623709475087358020837)
  ·
    refine ⟨904241945526578879628907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4822623709475087358020837 904241945526578879628907)
    ·
      refine ⟨1356362918289868319443361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904241945526578879628907 1356362918289868319443361)
      ·
        refine ⟨1017272188717401239582521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356362918289868319443361 1017272188717401239582521)
        ·
          refine ⟨762954141538050929686891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017272188717401239582521 762954141538050929686891)
          ·
            refine ⟨1144431212307076394530337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762954141538050929686891 1144431212307076394530337)
            ·
              refine ⟨858323409230307295897753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144431212307076394530337 858323409230307295897753)
              ·
                refine ⟨643742556922730471923315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858323409230307295897753 643742556922730471923315)
                ·
                  refine ⟨965613835384095707884973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643742556922730471923315 965613835384095707884973)
                  ·
                    refine ⟨362105188269035890456865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965613835384095707884973 362105188269035890456865)
                    ·
                      refine ⟨271578891201776917842649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362105188269035890456865 271578891201776917842649)
                      ·
                        rfl

theorem cell23_528898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_528898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528898 prefixEnd_528898 := by exact prefixLift 528898
  have htrace : WordTrace (prefixWord ++ tailWord_528898) baseStart_528898 baseEnd_528898 := by
    simpa [prefixWord, tailWord_528898, baseEnd_528898] using wordTrace_append hprefix tailTrace_528898
  have hstable : (prefixWord ++ tailWord_528898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528898).length < 2 ^ (prefixWord ++ tailWord_528898).sum := by decide
  have hdescent : baseEnd_528898 < baseStart_528898 := by decide
  rcases family_descends (prefixWord ++ tailWord_528898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528923 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_528923 : Nat := 118140960795 + 528923 * 2 ^ 59
def prefixEnd_528923 : Nat := 4983230072969 + 3 ^ 40 * 528923 * 2
def baseEnd_528923 : Nat := 271591728218139320030033

theorem tailTrace_528923 : CollatzResearch.WordTrace tailWord_528923 prefixEnd_528923 271591728218139320030033 := by
  unfold tailWord_528923
  simp only [CollatzResearch.WordTrace]
  refine ⟨19291406662809778701743423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12860937775206519134495615 19291406662809778701743423)
  ·
    refine ⟨28937109994214668052615135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19291406662809778701743423 28937109994214668052615135)
    ·
      refine ⟨43405664991322002078922703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28937109994214668052615135 43405664991322002078922703)
      ·
        refine ⟨65108497486983003118384055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43405664991322002078922703 65108497486983003118384055)
        ·
          refine ⟨97662746230474504677576083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65108497486983003118384055 97662746230474504677576083)
          ·
            refine ⟨146494119345711757016364125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97662746230474504677576083 146494119345711757016364125)
            ·
              refine ⟨54935294754641908881136547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146494119345711757016364125 54935294754641908881136547)
              ·
                refine ⟨82402942131962863321704821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54935294754641908881136547 82402942131962863321704821)
                ·
                  refine ⟨7725275824871518436409827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82402942131962863321704821 7725275824871518436409827)
                  ·
                    refine ⟨11587913737307277654614741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7725275824871518436409827 11587913737307277654614741)
                    ·
                      refine ⟨271591728218139320030033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11587913737307277654614741 271591728218139320030033)
                      ·
                        rfl

theorem cell23_528923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_528923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528923 prefixEnd_528923 := by exact prefixLift 528923
  have htrace : WordTrace (prefixWord ++ tailWord_528923) baseStart_528923 baseEnd_528923 := by
    simpa [prefixWord, tailWord_528923, baseEnd_528923] using wordTrace_append hprefix tailTrace_528923
  have hstable : (prefixWord ++ tailWord_528923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528923).length < 2 ^ (prefixWord ++ tailWord_528923).sum := by decide
  have hdescent : baseEnd_528923 < baseStart_528923 := by decide
  rcases family_descends (prefixWord ++ tailWord_528923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_528967 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_528967 : Nat := 118140960795 + 528967 * 2 ^ 59
def prefixEnd_528967 : Nat := 4983230072969 + 3 ^ 40 * 528967 * 2
def baseEnd_528967 : Nat := 271614321366937147879831

theorem tailTrace_528967 : CollatzResearch.WordTrace tailWord_528967 prefixEnd_528967 271614321366937147879831 := by
  unfold tailWord_528967
  simp only [CollatzResearch.WordTrace]
  refine ⟨19293011474650374216345155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12862007649766916144230103 19293011474650374216345155)
  ·
    refine ⟨28939517211975561324517733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19293011474650374216345155 28939517211975561324517733)
    ·
      refine ⟨5426159477245417748347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28939517211975561324517733 5426159477245417748347075)
      ·
        refine ⟨8139239215868126622520613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426159477245417748347075 8139239215868126622520613)
        ·
          refine ⟨1526107352975273741722615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8139239215868126622520613 1526107352975273741722615)
          ·
            refine ⟨2289161029462910612583923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526107352975273741722615 2289161029462910612583923)
            ·
              refine ⟨3433741544194365918875885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289161029462910612583923 3433741544194365918875885)
              ·
                refine ⟨1287653079072887219578457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3433741544194365918875885 1287653079072887219578457)
                ·
                  refine ⟨965739809304665414683843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287653079072887219578457 965739809304665414683843)
                  ·
                    refine ⟨1448609713956998122025765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 965739809304665414683843 1448609713956998122025765)
                    ·
                      refine ⟨271614321366937147879831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1448609713956998122025765 271614321366937147879831)
                      ·
                        rfl

theorem cell23_528967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_528967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_528967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_528967 prefixEnd_528967 := by exact prefixLift 528967
  have htrace : WordTrace (prefixWord ++ tailWord_528967) baseStart_528967 baseEnd_528967 := by
    simpa [prefixWord, tailWord_528967, baseEnd_528967] using wordTrace_append hprefix tailTrace_528967
  have hstable : (prefixWord ++ tailWord_528967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_528967).length < 2 ^ (prefixWord ++ tailWord_528967).sum := by decide
  have hdescent : baseEnd_528967 < baseStart_528967 := by decide
  rcases family_descends (prefixWord ++ tailWord_528967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529021 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_529021 : Nat := 118140960795 + 529021 * 2 ^ 59
def prefixEnd_529021 : Nat := 4983230072969 + 3 ^ 40 * 529021 * 2
def baseEnd_529021 : Nat := 271642049322279936604583

theorem tailTrace_529021 : CollatzResearch.WordTrace tailWord_529021 prefixEnd_529021 271642049322279936604583 := by
  unfold tailWord_529021
  simp only [CollatzResearch.WordTrace]
  refine ⟨19294981016454741438810917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12863320677636494292540611 19294981016454741438810917)
  ·
    refine ⟨3617808940585264019777047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19294981016454741438810917 3617808940585264019777047)
    ·
      refine ⟨5426713410877896029665571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617808940585264019777047 5426713410877896029665571)
      ·
        refine ⟨8140070116316844044498357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426713410877896029665571 8140070116316844044498357)
        ·
          refine ⟨763131573404704129171721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8140070116316844044498357 763131573404704129171721)
          ·
            refine ⟨572348680053528096878791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763131573404704129171721 572348680053528096878791)
            ·
              refine ⟨858523020080292145318187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572348680053528096878791 858523020080292145318187)
              ·
                refine ⟨1287784530120438217977281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858523020080292145318187 1287784530120438217977281)
                ·
                  refine ⟨965838397590328663482961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1287784530120438217977281 965838397590328663482961)
                  ·
                    refine ⟨724378798192746497612221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 965838397590328663482961 724378798192746497612221)
                    ·
                      refine ⟨271642049322279936604583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724378798192746497612221 271642049322279936604583)
                      ·
                        rfl

theorem cell23_529021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_529021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529021 prefixEnd_529021 := by exact prefixLift 529021
  have htrace : WordTrace (prefixWord ++ tailWord_529021) baseStart_529021 baseEnd_529021 := by
    simpa [prefixWord, tailWord_529021, baseEnd_529021] using wordTrace_append hprefix tailTrace_529021
  have hstable : (prefixWord ++ tailWord_529021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529021).length < 2 ^ (prefixWord ++ tailWord_529021).sum := by decide
  have hdescent : baseEnd_529021 < baseStart_529021 := by decide
  rcases family_descends (prefixWord ++ tailWord_529021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529128 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_529128 : Nat := 118140960795 + 529128 * 2 ^ 59
def prefixEnd_529128 : Nat := 4983230072969 + 3 ^ 40 * 529128 * 2
def baseEnd_529128 : Nat := 271696991752311017966591

theorem tailTrace_529128 : CollatzResearch.WordTrace tailWord_529128 prefixEnd_529128 271696991752311017966591 := by
  unfold tailWord_529128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9649441813533549356478019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12865922418044732475304025 9649441813533549356478019)
  ·
    refine ⟨14474162720300324034717029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9649441813533549356478019 14474162720300324034717029)
    ·
      refine ⟨2713905510056310756509443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14474162720300324034717029 2713905510056310756509443)
      ·
        refine ⟨4070858265084466134764165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713905510056310756509443 4070858265084466134764165)
        ·
          refine ⟨763285924703337400268281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4070858265084466134764165 763285924703337400268281)
          ·
            refine ⟨572464443527503050201211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763285924703337400268281 572464443527503050201211)
            ·
              refine ⟨858696665291254575301817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572464443527503050201211 858696665291254575301817)
              ·
                refine ⟨644022498968440931476363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858696665291254575301817 644022498968440931476363)
                ·
                  refine ⟨966033748452661397214545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644022498968440931476363 966033748452661397214545)
                  ·
                    refine ⟨724525311339496047910909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966033748452661397214545 724525311339496047910909)
                    ·
                      refine ⟨271696991752311017966591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724525311339496047910909 271696991752311017966591)
                      ·
                        rfl

theorem cell23_529128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_529128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529128 prefixEnd_529128 := by exact prefixLift 529128
  have htrace : WordTrace (prefixWord ++ tailWord_529128) baseStart_529128 baseEnd_529128 := by
    simpa [prefixWord, tailWord_529128, baseEnd_529128] using wordTrace_append hprefix tailTrace_529128
  have hstable : (prefixWord ++ tailWord_529128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529128).length < 2 ^ (prefixWord ++ tailWord_529128).sum := by decide
  have hdescent : baseEnd_529128 < baseStart_529128 := by decide
  rcases family_descends (prefixWord ++ tailWord_529128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529164 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_529164 : Nat := 118140960795 + 529164 * 2 ^ 59
def prefixEnd_529164 : Nat := 4983230072969 + 3 ^ 40 * 529164 * 2
def baseEnd_529164 : Nat := 271715477055872877116425

theorem tailTrace_529164 : CollatzResearch.WordTrace tailWord_529164 prefixEnd_529164 271715477055872877116425 := by
  unfold tailWord_529164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650098327468338430633273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12866797769957784574177697 9650098327468338430633273)
  ·
    refine ⟨7237573745601253822974955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9650098327468338430633273 7237573745601253822974955)
    ·
      refine ⟨10856360618401880734462433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7237573745601253822974955 10856360618401880734462433)
      ·
        refine ⟨8142270463801410550846825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10856360618401880734462433 8142270463801410550846825)
        ·
          refine ⟨6106702847851057913135119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8142270463801410550846825 6106702847851057913135119)
          ·
            refine ⟨9160054271776586869702679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106702847851057913135119 9160054271776586869702679)
            ·
              refine ⟨13740081407664880304554019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9160054271776586869702679 13740081407664880304554019)
              ·
                refine ⟨20610122111497320456831029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13740081407664880304554019 20610122111497320456831029)
                ·
                  refine ⟨1932198947952873792827909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20610122111497320456831029 1932198947952873792827909)
                  ·
                    refine ⟨362287302741163836155233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932198947952873792827909 362287302741163836155233)
                    ·
                      refine ⟨271715477055872877116425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362287302741163836155233 271715477055872877116425)
                      ·
                        rfl

theorem cell23_529164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_529164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529164 prefixEnd_529164 := by exact prefixLift 529164
  have htrace : WordTrace (prefixWord ++ tailWord_529164) baseStart_529164 baseEnd_529164 := by
    simpa [prefixWord, tailWord_529164, baseEnd_529164] using wordTrace_append hprefix tailTrace_529164
  have hstable : (prefixWord ++ tailWord_529164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529164).length < 2 ^ (prefixWord ++ tailWord_529164).sum := by decide
  have hdescent : baseEnd_529164 < baseStart_529164 := by decide
  rcases family_descends (prefixWord ++ tailWord_529164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529167 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_529167 : Nat := 118140960795 + 529167 * 2 ^ 59
def prefixEnd_529167 : Nat := 4983230072969 + 3 ^ 40 * 529167 * 2
def baseEnd_529167 : Nat := 271717017497836365378911

theorem tailTrace_529167 : CollatzResearch.WordTrace tailWord_529167 prefixEnd_529167 271717017497836365378911 := by
  unfold tailWord_529167
  simp only [CollatzResearch.WordTrace]
  refine ⟨19300306073925808373625755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12866870715950538915750503 19300306073925808373625755)
  ·
    refine ⟨28950459110888712560438633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19300306073925808373625755 28950459110888712560438633)
    ·
      refine ⟨21712844333166534420328975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28950459110888712560438633 21712844333166534420328975)
      ·
        refine ⟨32569266499749801630493463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21712844333166534420328975 32569266499749801630493463)
        ·
          refine ⟨48853899749624702445740195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32569266499749801630493463 48853899749624702445740195)
          ·
            refine ⟨73280849624437053668610293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48853899749624702445740195 73280849624437053668610293)
            ·
              refine ⟨6870079652290973781432215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73280849624437053668610293 6870079652290973781432215)
              ·
                refine ⟨10305119478436460672148323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870079652290973781432215 10305119478436460672148323)
                ·
                  refine ⟨15457679217654691008222485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10305119478436460672148323 15457679217654691008222485)
                  ·
                    refine ⟨724578713327563641010429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15457679217654691008222485 724578713327563641010429)
                    ·
                      refine ⟨271717017497836365378911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724578713327563641010429 271717017497836365378911)
                      ·
                        rfl

theorem cell23_529167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_529167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529167 prefixEnd_529167 := by exact prefixLift 529167
  have htrace : WordTrace (prefixWord ++ tailWord_529167) baseStart_529167 baseEnd_529167 := by
    simpa [prefixWord, tailWord_529167, baseEnd_529167] using wordTrace_append hprefix tailTrace_529167
  have hstable : (prefixWord ++ tailWord_529167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529167).length < 2 ^ (prefixWord ++ tailWord_529167).sum := by decide
  have hdescent : baseEnd_529167 < baseStart_529167 := by decide
  rcases family_descends (prefixWord ++ tailWord_529167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529198 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_529198 : Nat := 118140960795 + 529198 * 2 ^ 59
def prefixEnd_529198 : Nat := 4983230072969 + 3 ^ 40 * 529198 * 2
def baseEnd_529198 : Nat := 271732935398125744091269

theorem tailTrace_529198 : CollatzResearch.WordTrace tailWord_529198 prefixEnd_529198 271732935398125744091269 := by
  unfold tailWord_529198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412679592101687583500531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12867624491209000445336165 2412679592101687583500531)
  ·
    refine ⟨3619019388152531375250797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412679592101687583500531 3619019388152531375250797)
    ·
      refine ⟨1357132270557199265719049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3619019388152531375250797 1357132270557199265719049)
      ·
        refine ⟨1017849202917899449289287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1357132270557199265719049 1017849202917899449289287)
        ·
          refine ⟨1526773804376849173933931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017849202917899449289287 1526773804376849173933931)
          ·
            refine ⟨2290160706565273760900897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526773804376849173933931 2290160706565273760900897)
            ·
              refine ⟨1717620529923955320675673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290160706565273760900897 1717620529923955320675673)
              ·
                refine ⟨1288215397442966490506755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1717620529923955320675673 1288215397442966490506755)
                ·
                  refine ⟨1932323096164449735760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288215397442966490506755 1932323096164449735760133)
                  ·
                    refine ⟨362310580530834325455025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1932323096164449735760133 362310580530834325455025)
                    ·
                      refine ⟨271732935398125744091269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362310580530834325455025 271732935398125744091269)
                      ·
                        rfl

theorem cell23_529198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_529198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529198 prefixEnd_529198 := by exact prefixLift 529198
  have htrace : WordTrace (prefixWord ++ tailWord_529198) baseStart_529198 baseEnd_529198 := by
    simpa [prefixWord, tailWord_529198, baseEnd_529198] using wordTrace_append hprefix tailTrace_529198
  have hstable : (prefixWord ++ tailWord_529198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529198).length < 2 ^ (prefixWord ++ tailWord_529198).sum := by decide
  have hdescent : baseEnd_529198 < baseStart_529198 := by decide
  rcases family_descends (prefixWord ++ tailWord_529198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529215 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 2, 2, 2]
def baseStart_529215 : Nat := 118140960795 + 529215 * 2 ^ 59
def prefixEnd_529215 : Nat := 4983230072969 + 3 ^ 40 * 529215 * 2
def baseEnd_529215 : Nat := 271741664569252177578691

theorem tailTrace_529215 : CollatzResearch.WordTrace tailWord_529215 prefixEnd_529215 271741664569252177578691 := by
  unfold tailWord_529215
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302056777751912571373099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12868037851834608380915399 19302056777751912571373099)
  ·
    refine ⟨28953085166627868857059649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302056777751912571373099 28953085166627868857059649)
    ·
      refine ⟨21714813874970901642794737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28953085166627868857059649 21714813874970901642794737)
      ·
        refine ⟨16286110406228176232096053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21714813874970901642794737 16286110406228176232096053)
        ·
          refine ⟨1526822850583891521759005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16286110406228176232096053 1526822850583891521759005)
          ·
            refine ⟨572558568968959320659627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526822850583891521759005 572558568968959320659627)
            ·
              refine ⟨858837853453438980989441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572558568968959320659627 858837853453438980989441)
              ·
                refine ⟨644128390090079235742081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858837853453438980989441 644128390090079235742081)
                ·
                  refine ⟨483096292567559426806561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644128390090079235742081 483096292567559426806561)
                  ·
                    refine ⟨362322219425669570104921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483096292567559426806561 362322219425669570104921)
                    ·
                      refine ⟨271741664569252177578691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362322219425669570104921 271741664569252177578691)
                      ·
                        rfl

theorem cell23_529215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_529215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529215 prefixEnd_529215 := by exact prefixLift 529215
  have htrace : WordTrace (prefixWord ++ tailWord_529215) baseStart_529215 baseEnd_529215 := by
    simpa [prefixWord, tailWord_529215, baseEnd_529215] using wordTrace_append hprefix tailTrace_529215
  have hstable : (prefixWord ++ tailWord_529215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529215).length < 2 ^ (prefixWord ++ tailWord_529215).sum := by decide
  have hdescent : baseEnd_529215 < baseStart_529215 := by decide
  rcases family_descends (prefixWord ++ tailWord_529215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529247 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 8]
def baseStart_529247 : Nat := 118140960795 + 529247 * 2 ^ 59
def prefixEnd_529247 : Nat := 4983230072969 + 3 ^ 40 * 529247 * 2
def baseEnd_529247 : Nat := 90586031983398684126181

theorem tailTrace_529247 : CollatzResearch.WordTrace tailWord_529247 prefixEnd_529247 90586031983398684126181 := by
  unfold tailWord_529247
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303223913635982036537995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12868815942423988024358663 19303223913635982036537995)
  ·
    refine ⟨28954835870453973054806993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19303223913635982036537995 28954835870453973054806993)
    ·
      refine ⟨21716126902840479791105245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28954835870453973054806993 21716126902840479791105245)
      ·
        refine ⟨8143547588565179921664467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21716126902840479791105245 8143547588565179921664467)
        ·
          refine ⟨12215321382847769882496701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143547588565179921664467 12215321382847769882496701)
          ·
            refine ⟨4580745518567913705936263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12215321382847769882496701 4580745518567913705936263)
            ·
              refine ⟨6871118277851870558904395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580745518567913705936263 6871118277851870558904395)
              ·
                refine ⟨10306677416777805838356593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871118277851870558904395 10306677416777805838356593)
                ·
                  refine ⟨7730008062583354378767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10306677416777805838356593 7730008062583354378767445)
                  ·
                    refine ⟨90586031983398684126181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7730008062583354378767445 90586031983398684126181)
                    ·
                      rfl

theorem cell23_529247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_529247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529247 prefixEnd_529247 := by exact prefixLift 529247
  have htrace : WordTrace (prefixWord ++ tailWord_529247) baseStart_529247 baseEnd_529247 := by
    simpa [prefixWord, tailWord_529247, baseEnd_529247] using wordTrace_append hprefix tailTrace_529247
  have hstable : (prefixWord ++ tailWord_529247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529247).length < 2 ^ (prefixWord ++ tailWord_529247).sum := by decide
  have hdescent : baseEnd_529247 < baseStart_529247 := by decide
  rcases family_descends (prefixWord ++ tailWord_529247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529257 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_529257 : Nat := 118140960795 + 529257 * 2 ^ 59
def prefixEnd_529257 : Nat := 4983230072969 + 3 ^ 40 * 529257 * 2
def baseEnd_529257 : Nat := 271763230756741013253497

theorem tailTrace_529257 : CollatzResearch.WordTrace tailWord_529257 prefixEnd_529257 271763230756741013253497 := by
  unfold tailWord_529257
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303588643599753744402025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12869059095733169162934683 19303588643599753744402025)
  ·
    refine ⟨14477691482699815308301519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19303588643599753744402025 14477691482699815308301519)
    ·
      refine ⟨21716537224049722962452279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14477691482699815308301519 21716537224049722962452279)
      ·
        refine ⟨32574805836074584443678419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21716537224049722962452279 32574805836074584443678419)
        ·
          refine ⟨48862208754111876665517629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32574805836074584443678419 48862208754111876665517629)
          ·
            refine ⟨18323328282791953749569111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48862208754111876665517629 18323328282791953749569111)
            ·
              refine ⟨27484992424187930624353667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18323328282791953749569111 27484992424187930624353667)
              ·
                refine ⟨41227488636281895936530501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27484992424187930624353667 41227488636281895936530501)
                ·
                  refine ⟨7730154119302855488099469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41227488636281895936530501 7730154119302855488099469)
                  ·
                    refine ⟨2898807794738570808037301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7730154119302855488099469 2898807794738570808037301)
                    ·
                      refine ⟨271763230756741013253497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2898807794738570808037301 271763230756741013253497)
                      ·
                        rfl

theorem cell23_529257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_529257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529257 prefixEnd_529257 := by exact prefixLift 529257
  have htrace : WordTrace (prefixWord ++ tailWord_529257) baseStart_529257 baseEnd_529257 := by
    simpa [prefixWord, tailWord_529257, baseEnd_529257] using wordTrace_append hprefix tailTrace_529257
  have hstable : (prefixWord ++ tailWord_529257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529257).length < 2 ^ (prefixWord ++ tailWord_529257).sum := by decide
  have hdescent : baseEnd_529257 < baseStart_529257 := by decide
  rcases family_descends (prefixWord ++ tailWord_529257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529264 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_529264 : Nat := 118140960795 + 529264 * 2 ^ 59
def prefixEnd_529264 : Nat := 4983230072969 + 3 ^ 40 * 529264 * 2
def baseEnd_529264 : Nat := 90588941707107495288655

theorem tailTrace_529264 : CollatzResearch.WordTrace tailWord_529264 prefixEnd_529264 90588941707107495288655 := by
  unfold tailWord_529264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651921977287196969953423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12869229303049595959937897 9651921977287196969953423)
  ·
    refine ⟨14477882965930795454930135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9651921977287196969953423 14477882965930795454930135)
    ·
      refine ⟨21716824448896193182395203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14477882965930795454930135 21716824448896193182395203)
      ·
        refine ⟨32575236673344289773592805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21716824448896193182395203 32575236673344289773592805)
        ·
          refine ⟨6107856876252054332548651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32575236673344289773592805 6107856876252054332548651)
          ·
            refine ⟨9161785314378081498822977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107856876252054332548651 9161785314378081498822977)
            ·
              refine ⟨6871338985783561124117233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9161785314378081498822977 6871338985783561124117233)
              ·
                refine ⟨5153504239337670843087925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6871338985783561124117233 5153504239337670843087925)
                ·
                  refine ⟨483141022437906641539493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5153504239337670843087925 483141022437906641539493)
                  ·
                    refine ⟨90588941707107495288655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483141022437906641539493 90588941707107495288655)
                    ·
                      rfl

theorem cell23_529264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_529264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529264 prefixEnd_529264 := by exact prefixLift 529264
  have htrace : WordTrace (prefixWord ++ tailWord_529264) baseStart_529264 baseEnd_529264 := by
    simpa [prefixWord, tailWord_529264, baseEnd_529264] using wordTrace_append hprefix tailTrace_529264
  have hstable : (prefixWord ++ tailWord_529264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529264).length < 2 ^ (prefixWord ++ tailWord_529264).sum := by decide
  have hdescent : baseEnd_529264 < baseStart_529264 := by decide
  rcases family_descends (prefixWord ++ tailWord_529264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529267 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_529267 : Nat := 118140960795 + 529267 * 2 ^ 59
def prefixEnd_529267 : Nat := 4983230072969 + 3 ^ 40 * 529267 * 2
def baseEnd_529267 : Nat := 271768365563285974128451

theorem tailTrace_529267 : CollatzResearch.WordTrace tailWord_529267 prefixEnd_529267 271768365563285974128451 := by
  unfold tailWord_529267
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303953373563525452266055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12869302249042350301510703 19303953373563525452266055)
  ·
    refine ⟨28955930060345288178399083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19303953373563525452266055 28955930060345288178399083)
    ·
      refine ⟨43433895090517932267598625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28955930060345288178399083 43433895090517932267598625)
      ·
        refine ⟨32575421317888449200698969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43433895090517932267598625 32575421317888449200698969)
        ·
          refine ⟨24431565988416336900524227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32575421317888449200698969 24431565988416336900524227)
          ·
            refine ⟨36647348982624505350786341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24431565988416336900524227 36647348982624505350786341)
            ·
              refine ⟨6871377934242094753272439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36647348982624505350786341 6871377934242094753272439)
              ·
                refine ⟨10307066901363142129908659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871377934242094753272439 10307066901363142129908659)
                ·
                  refine ⟨15460600352044713194862989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10307066901363142129908659 15460600352044713194862989)
                  ·
                    refine ⟨5797725132016767448073621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15460600352044713194862989 5797725132016767448073621)
                    ·
                      refine ⟨271768365563285974128451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5797725132016767448073621 271768365563285974128451)
                      ·
                        rfl

theorem cell23_529267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_529267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529267 prefixEnd_529267 := by exact prefixLift 529267
  have htrace : WordTrace (prefixWord ++ tailWord_529267) baseStart_529267 baseEnd_529267 := by
    simpa [prefixWord, tailWord_529267, baseEnd_529267] using wordTrace_append hprefix tailTrace_529267
  have hstable : (prefixWord ++ tailWord_529267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529267).length < 2 ^ (prefixWord ++ tailWord_529267).sum := by decide
  have hdescent : baseEnd_529267 < baseStart_529267 := by decide
  rcases family_descends (prefixWord ++ tailWord_529267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529278 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_529278 : Nat := 118140960795 + 529278 * 2 ^ 59
def prefixEnd_529278 : Nat := 4983230072969 + 3 ^ 40 * 529278 * 2
def baseEnd_529278 : Nat := 271774013850485431090901

theorem tailTrace_529278 : CollatzResearch.WordTrace tailWord_529278 prefixEnd_529278 271774013850485431090901 := by
  unfold tailWord_529278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413044322065459291364561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12869569717682449553944325 2413044322065459291364561)
  ·
    refine ⟨1809783241549094468523421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2413044322065459291364561 1809783241549094468523421)
    ·
      refine ⟨678668715580910425696283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1809783241549094468523421 678668715580910425696283)
      ·
        refine ⟨1018003073371365638544425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678668715580910425696283 1018003073371365638544425)
        ·
          refine ⟨763502305028524228908319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018003073371365638544425 763502305028524228908319)
          ·
            refine ⟨1145253457542786343362479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763502305028524228908319 1145253457542786343362479)
            ·
              refine ⟨1717880186314179515043719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145253457542786343362479 1717880186314179515043719)
              ·
                refine ⟨2576820279471269272565579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1717880186314179515043719 2576820279471269272565579)
                ·
                  refine ⟨3865230419206903908848369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576820279471269272565579 3865230419206903908848369)
                  ·
                    refine ⟨2898922814405177931636277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865230419206903908848369 2898922814405177931636277)
                    ·
                      refine ⟨271774013850485431090901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2898922814405177931636277 271774013850485431090901)
                      ·
                        rfl

theorem cell23_529278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_529278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529278 prefixEnd_529278 := by exact prefixLift 529278
  have htrace : WordTrace (prefixWord ++ tailWord_529278) baseStart_529278 baseEnd_529278 := by
    simpa [prefixWord, tailWord_529278, baseEnd_529278] using wordTrace_append hprefix tailTrace_529278
  have hstable : (prefixWord ++ tailWord_529278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529278).length < 2 ^ (prefixWord ++ tailWord_529278).sum := by decide
  have hdescent : baseEnd_529278 < baseStart_529278 := by decide
  rcases family_descends (prefixWord ++ tailWord_529278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529331 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 4, 3, 2]
def baseStart_529331 : Nat := 118140960795 + 529331 * 2 ^ 59
def prefixEnd_529331 : Nat := 4983230072969 + 3 ^ 40 * 529331 * 2
def baseEnd_529331 : Nat := 271801228325173723728157

theorem tailTrace_529331 : CollatzResearch.WordTrace tailWord_529331 prefixEnd_529331 271801228325173723728157 := by
  unfold tailWord_529331
  simp only [CollatzResearch.WordTrace]
  refine ⟨19306287645331664382595847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12870858430221109588397231 19306287645331664382595847)
  ·
    refine ⟨28959431467997496573893771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19306287645331664382595847 28959431467997496573893771)
    ·
      refine ⟨43439147201996244860840657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28959431467997496573893771 43439147201996244860840657)
      ·
        refine ⟨32579360401497183645630493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43439147201996244860840657 32579360401497183645630493)
        ·
          refine ⟨12217260150561443867111435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32579360401497183645630493 12217260150561443867111435)
          ·
            refine ⟨18325890225842165800667153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217260150561443867111435 18325890225842165800667153)
            ·
              refine ⟨13744417669381624350500365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18325890225842165800667153 13744417669381624350500365)
              ·
                refine ⟨5154156626018109131437637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13744417669381624350500365 5154156626018109131437637)
                ·
                  refine ⟨966404367378395462144557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5154156626018109131437637 966404367378395462144557)
                  ·
                    refine ⟨362401637766898298304209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 966404367378395462144557 362401637766898298304209)
                    ·
                      refine ⟨271801228325173723728157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362401637766898298304209 271801228325173723728157)
                      ·
                        rfl

theorem cell23_529331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 3, 2].length) (baseStart_529331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529331 prefixEnd_529331 := by exact prefixLift 529331
  have htrace : WordTrace (prefixWord ++ tailWord_529331) baseStart_529331 baseEnd_529331 := by
    simpa [prefixWord, tailWord_529331, baseEnd_529331] using wordTrace_append hprefix tailTrace_529331
  have hstable : (prefixWord ++ tailWord_529331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529331).length < 2 ^ (prefixWord ++ tailWord_529331).sum := by decide
  have hdescent : baseEnd_529331 < baseStart_529331 := by decide
  rcases family_descends (prefixWord ++ tailWord_529331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529332 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_529332 : Nat := 118140960795 + 529332 * 2 ^ 59
def prefixEnd_529332 : Nat := 4983230072969 + 3 ^ 40 * 529332 * 2
def baseEnd_529332 : Nat := 90600580601942739938551

theorem tailTrace_529332 : CollatzResearch.WordTrace tailWord_529332 prefixEnd_529332 90600580601942739938551 := by
  unfold tailWord_529332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653162059164020776691125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12870882745552027702254833 9653162059164020776691125)
  ·
    refine ⟨904983943046626947814793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9653162059164020776691125 904983943046626947814793)
    ·
      refine ⟨678737957284970210861095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904983943046626947814793 678737957284970210861095)
      ·
        refine ⟨1018106935927455316291643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678737957284970210861095 1018106935927455316291643)
        ·
          refine ⟨1527160403891182974437465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018106935927455316291643 1527160403891182974437465)
          ·
            refine ⟨1145370302918387230828099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527160403891182974437465 1145370302918387230828099)
            ·
              refine ⟨1718055454377580846242149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145370302918387230828099 1718055454377580846242149)
              ·
                refine ⟨322135397695796408670403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1718055454377580846242149 322135397695796408670403)
                ·
                  refine ⟨483203096543694613005605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322135397695796408670403 483203096543694613005605)
                  ·
                    refine ⟨90600580601942739938551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483203096543694613005605 90600580601942739938551)
                    ·
                      rfl

theorem cell23_529332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_529332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529332 prefixEnd_529332 := by exact prefixLift 529332
  have htrace : WordTrace (prefixWord ++ tailWord_529332) baseStart_529332 baseEnd_529332 := by
    simpa [prefixWord, tailWord_529332, baseEnd_529332] using wordTrace_append hprefix tailTrace_529332
  have hstable : (prefixWord ++ tailWord_529332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529332).length < 2 ^ (prefixWord ++ tailWord_529332).sum := by decide
  have hdescent : baseEnd_529332 < baseStart_529332 := by decide
  rcases family_descends (prefixWord ++ tailWord_529332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529361 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_529361 : Nat := 118140960795 + 529361 * 2 ^ 59
def prefixEnd_529361 : Nat := 4983230072969 + 3 ^ 40 * 529361 * 2
def baseEnd_529361 : Nat := 271816632744808606353019

theorem tailTrace_529361 : CollatzResearch.WordTrace tailWord_529361 prefixEnd_529361 271816632744808606353019 := by
  unfold tailWord_529361
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307381835222979506187937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12871587890148653004125291 19307381835222979506187937)
  ·
    refine ⟨14480536376417234629640953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19307381835222979506187937 14480536376417234629640953)
    ·
      refine ⟨10860402282312925972230715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14480536376417234629640953 10860402282312925972230715)
      ·
        refine ⟨16290603423469388958346073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10860402282312925972230715 16290603423469388958346073)
        ·
          refine ⟨12217952567602041718759555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16290603423469388958346073 12217952567602041718759555)
          ·
            refine ⟨18326928851403062578139333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217952567602041718759555 18326928851403062578139333)
            ·
              refine ⟨3436299159638074233401125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18326928851403062578139333 3436299159638074233401125)
              ·
                refine ⟨644306092432138918762711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3436299159638074233401125 644306092432138918762711)
                ·
                  refine ⟨966459138648208378144067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644306092432138918762711 966459138648208378144067)
                  ·
                    refine ⟨1449688707972312567216101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 966459138648208378144067 1449688707972312567216101)
                    ·
                      refine ⟨271816632744808606353019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1449688707972312567216101 271816632744808606353019)
                      ·
                        rfl

theorem cell23_529361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_529361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529361 prefixEnd_529361 := by exact prefixLift 529361
  have htrace : WordTrace (prefixWord ++ tailWord_529361) baseStart_529361 baseEnd_529361 := by
    simpa [prefixWord, tailWord_529361, baseEnd_529361] using wordTrace_append hprefix tailTrace_529361
  have hstable : (prefixWord ++ tailWord_529361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529361).length < 2 ^ (prefixWord ++ tailWord_529361).sum := by decide
  have hdescent : baseEnd_529361 < baseStart_529361 := by decide
  rcases family_descends (prefixWord ++ tailWord_529361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529375 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 1, 5]
def baseStart_529375 : Nat := 118140960795 + 529375 * 2 ^ 59
def prefixEnd_529375 : Nat := 4983230072969 + 3 ^ 40 * 529375 * 2
def baseEnd_529375 : Nat := 90607940491323850525985

theorem tailTrace_529375 : CollatzResearch.WordTrace tailWord_529375 prefixEnd_529375 90607940491323850525985 := by
  unfold tailWord_529375
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307892457172259897197579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12871928304781506598131719 19307892457172259897197579)
  ·
    refine ⟨28961838685758389845796369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19307892457172259897197579 28961838685758389845796369)
    ·
      refine ⟨21721379014318792384347277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28961838685758389845796369 21721379014318792384347277)
      ·
        refine ⟨8145517130369547144130229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21721379014318792384347277 8145517130369547144130229)
        ·
          refine ⟨763642230972145044762209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8145517130369547144130229 763642230972145044762209)
          ·
            refine ⟨572731673229108783571657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763642230972145044762209 572731673229108783571657)
            ·
              refine ⟨429548754921831587678743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572731673229108783571657 429548754921831587678743)
              ·
                refine ⟨644323132382747381518115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429548754921831587678743 644323132382747381518115)
                ·
                  refine ⟨966484698574121072277173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644323132382747381518115 966484698574121072277173)
                  ·
                    refine ⟨90607940491323850525985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 966484698574121072277173 90607940491323850525985)
                    ·
                      rfl

theorem cell23_529375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_529375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529375 prefixEnd_529375 := by exact prefixLift 529375
  have htrace : WordTrace (prefixWord ++ tailWord_529375) baseStart_529375 baseEnd_529375 := by
    simpa [prefixWord, tailWord_529375, baseEnd_529375] using wordTrace_append hprefix tailTrace_529375
  have hstable : (prefixWord ++ tailWord_529375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529375).length < 2 ^ (prefixWord ++ tailWord_529375).sum := by decide
  have hdescent : baseEnd_529375 < baseStart_529375 := by decide
  rcases family_descends (prefixWord ++ tailWord_529375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529398 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_529398 : Nat := 118140960795 + 529398 * 2 ^ 59
def prefixEnd_529398 : Nat := 4983230072969 + 3 ^ 40 * 529398 * 2
def baseEnd_529398 : Nat := 271835631529024961590349

theorem tailTrace_529398 : CollatzResearch.WordTrace tailWord_529398 prefixEnd_529398 271835631529024961590349 := by
  unfold tailWord_529398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206795708505558426580303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12872487557392623216856565 1206795708505558426580303)
  ·
    refine ⟨1810193562758337639870455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206795708505558426580303 1810193562758337639870455)
    ·
      refine ⟨2715290344137506459805683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810193562758337639870455 2715290344137506459805683)
      ·
        refine ⟨4072935516206259689708525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2715290344137506459805683 4072935516206259689708525)
        ·
          refine ⟨1527350818577347383640697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072935516206259689708525 1527350818577347383640697)
          ·
            refine ⟨1145513113933010537730523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1527350818577347383640697 1145513113933010537730523)
            ·
              refine ⟨1718269670899515806595785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145513113933010537730523 1718269670899515806595785)
              ·
                refine ⟨1288702253174636854946839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718269670899515806595785 1288702253174636854946839)
                ·
                  refine ⟨1933053379761955282420259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288702253174636854946839 1933053379761955282420259)
                  ·
                    refine ⟨2899580069642932923630389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933053379761955282420259 2899580069642932923630389)
                    ·
                      refine ⟨271835631529024961590349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2899580069642932923630389 271835631529024961590349)
                      ·
                        rfl

theorem cell23_529398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_529398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529398 prefixEnd_529398 := by exact prefixLift 529398
  have htrace : WordTrace (prefixWord ++ tailWord_529398) baseStart_529398 baseEnd_529398 := by
    simpa [prefixWord, tailWord_529398, baseEnd_529398] using wordTrace_append hprefix tailTrace_529398
  have hstable : (prefixWord ++ tailWord_529398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529398).length < 2 ^ (prefixWord ++ tailWord_529398).sum := by decide
  have hdescent : baseEnd_529398 < baseStart_529398 := by decide
  rcases family_descends (prefixWord ++ tailWord_529398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529418 : List Nat := [3, 1, 2, 2, 3, 3, 2, 7]
def baseStart_529418 : Nat := 118140960795 + 529418 * 2 ^ 59
def prefixEnd_529418 : Nat := 4983230072969 + 3 ^ 40 * 529418 * 2
def baseEnd_529418 : Nat := 10068366708967217901491

theorem tailTrace_529418 : CollatzResearch.WordTrace tailWord_529418 prefixEnd_529418 10068366708967217901491 := by
  unfold tailWord_529418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827365199004119560253227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12872973864010985494008605 4827365199004119560253227)
  ·
    refine ⟨7241047798506179340379841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827365199004119560253227 7241047798506179340379841)
    ·
      refine ⟨5430785848879634505284881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7241047798506179340379841 5430785848879634505284881)
      ·
        refine ⟨4073089386659725878963661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5430785848879634505284881 4073089386659725878963661)
        ·
          refine ⟨1527408519997397204611373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4073089386659725878963661 1527408519997397204611373)
          ·
            refine ⟨572778194999023951729265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1527408519997397204611373 572778194999023951729265)
            ·
              refine ⟨429583646249267963796949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572778194999023951729265 429583646249267963796949)
              ·
                refine ⟨10068366708967217901491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 429583646249267963796949 10068366708967217901491)
                ·
                  rfl

theorem cell23_529418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_529418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529418 prefixEnd_529418 := by exact prefixLift 529418
  have htrace : WordTrace (prefixWord ++ tailWord_529418) baseStart_529418 baseEnd_529418 := by
    simpa [prefixWord, tailWord_529418, baseEnd_529418] using wordTrace_append hprefix tailTrace_529418
  have hstable : (prefixWord ++ tailWord_529418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529418).length < 2 ^ (prefixWord ++ tailWord_529418).sum := by decide
  have hdescent : baseEnd_529418 < baseStart_529418 := by decide
  rcases family_descends (prefixWord ++ tailWord_529418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529429 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_529429 : Nat := 118140960795 + 529429 * 2 ^ 59
def prefixEnd_529429 : Nat := 4983230072969 + 3 ^ 40 * 529429 * 2
def baseEnd_529429 : Nat := 271851549429314340302707

theorem tailTrace_529429 : CollatzResearch.WordTrace tailWord_529429 prefixEnd_529429 271851549429314340302707 := by
  unfold tailWord_529429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309861998976627119663341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12873241332651084746442227 19309861998976627119663341)
  ·
    refine ⟨7241198249616235169873753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19309861998976627119663341 7241198249616235169873753)
    ·
      refine ⟨5430898687212176377405315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7241198249616235169873753 5430898687212176377405315)
      ·
        refine ⟨8146348030818264566107973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430898687212176377405315 8146348030818264566107973)
        ·
          refine ⟨1527440255778424606145245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8146348030818264566107973 1527440255778424606145245)
          ·
            refine ⟨572790095916909227304467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1527440255778424606145245 572790095916909227304467)
            ·
              refine ⟨859185143875363840956701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572790095916909227304467 859185143875363840956701)
              ·
                refine ⟨322194428953261440358763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859185143875363840956701 322194428953261440358763)
                ·
                  refine ⟨483291643429892160538145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322194428953261440358763 483291643429892160538145)
                  ·
                    refine ⟨362468732572419120403609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483291643429892160538145 362468732572419120403609)
                    ·
                      refine ⟨271851549429314340302707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362468732572419120403609 271851549429314340302707)
                      ·
                        rfl

theorem cell23_529429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_529429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529429 prefixEnd_529429 := by exact prefixLift 529429
  have htrace : WordTrace (prefixWord ++ tailWord_529429) baseStart_529429 baseEnd_529429 := by
    simpa [prefixWord, tailWord_529429, baseEnd_529429] using wordTrace_append hprefix tailTrace_529429
  have hstable : (prefixWord ++ tailWord_529429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529429).length < 2 ^ (prefixWord ++ tailWord_529429).sum := by decide
  have hdescent : baseEnd_529429 < baseStart_529429 := by decide
  rcases family_descends (prefixWord ++ tailWord_529429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529462 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_529462 : Nat := 118140960795 + 529462 * 2 ^ 59
def prefixEnd_529462 : Nat := 4983230072969 + 3 ^ 40 * 529462 * 2
def baseEnd_529462 : Nat := 271868494290912711190055

theorem tailTrace_529462 : CollatzResearch.WordTrace tailWord_529462 prefixEnd_529462 271868494290912711190055 := by
  unfold tailWord_529462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206941600491067109725915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12874043738571382503743093 1206941600491067109725915)
  ·
    refine ⟨1810412400736600664588873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206941600491067109725915 1810412400736600664588873)
    ·
      refine ⟨1357809300552450498441655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1810412400736600664588873 1357809300552450498441655)
      ·
        refine ⟨2036713950828675747662483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357809300552450498441655 2036713950828675747662483)
        ·
          refine ⟨3055070926243013621493725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036713950828675747662483 3055070926243013621493725)
          ·
            refine ⟨1145651597341130108060147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3055070926243013621493725 1145651597341130108060147)
            ·
              refine ⟨1718477396011695162090221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145651597341130108060147 1718477396011695162090221)
              ·
                refine ⟨644429023504385685783833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718477396011695162090221 644429023504385685783833)
                ·
                  refine ⟨483321767628289264337875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644429023504385685783833 483321767628289264337875)
                  ·
                    refine ⟨724982651442433896506813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 483321767628289264337875 724982651442433896506813)
                    ·
                      refine ⟨271868494290912711190055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 724982651442433896506813 271868494290912711190055)
                      ·
                        rfl

theorem cell23_529462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_529462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529462 prefixEnd_529462 := by exact prefixLift 529462
  have htrace : WordTrace (prefixWord ++ tailWord_529462) baseStart_529462 baseEnd_529462 := by
    simpa [prefixWord, tailWord_529462, baseEnd_529462] using wordTrace_append hprefix tailTrace_529462
  have hstable : (prefixWord ++ tailWord_529462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529462).length < 2 ^ (prefixWord ++ tailWord_529462).sum := by decide
  have hdescent : baseEnd_529462 < baseStart_529462 := by decide
  rcases family_descends (prefixWord ++ tailWord_529462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529485 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_529485 : Nat := 118140960795 + 529485 * 2 ^ 59
def prefixEnd_529485 : Nat := 4983230072969 + 3 ^ 40 * 529485 * 2
def baseEnd_529485 : Nat := 271880304345966121202449

theorem tailTrace_529485 : CollatzResearch.WordTrace tailWord_529485 prefixEnd_529485 271880304345966121202449 := by
  unfold tailWord_529485
  simp only [CollatzResearch.WordTrace]
  refine ⟨19311904486773748683701909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12874602991182499122467939 19311904486773748683701909)
  ·
    refine ⟨905245522817519469548527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19311904486773748683701909 905245522817519469548527)
    ·
      refine ⟨1357868284226279204322791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 905245522817519469548527 1357868284226279204322791)
      ·
        refine ⟨2036802426339418806484187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357868284226279204322791 2036802426339418806484187)
        ·
          refine ⟨3055203639509128209726281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036802426339418806484187 3055203639509128209726281)
          ·
            refine ⟨2291402729631846157294711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055203639509128209726281 2291402729631846157294711)
            ·
              refine ⟨3437104094447769235942067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291402729631846157294711 3437104094447769235942067)
              ·
                refine ⟨5155656141671653853913101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437104094447769235942067 5155656141671653853913101)
                ·
                  refine ⟨1933371053126870195217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5155656141671653853913101 1933371053126870195217413)
                  ·
                    refine ⟨362507072461288161603265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1933371053126870195217413 362507072461288161603265)
                    ·
                      refine ⟨271880304345966121202449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362507072461288161603265 271880304345966121202449)
                      ·
                        rfl

theorem cell23_529485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_529485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529485 prefixEnd_529485 := by exact prefixLift 529485
  have htrace : WordTrace (prefixWord ++ tailWord_529485) baseStart_529485 baseEnd_529485 := by
    simpa [prefixWord, tailWord_529485, baseEnd_529485] using wordTrace_append hprefix tailTrace_529485
  have hstable : (prefixWord ++ tailWord_529485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529485).length < 2 ^ (prefixWord ++ tailWord_529485).sum := by decide
  have hdescent : baseEnd_529485 < baseStart_529485 := by decide
  rcases family_descends (prefixWord ++ tailWord_529485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529518 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_529518 : Nat := 118140960795 + 529518 * 2 ^ 59
def prefixEnd_529518 : Nat := 4983230072969 + 3 ^ 40 * 529518 * 2
def baseEnd_529518 : Nat := 271897249207564492089797

theorem tailTrace_529518 : CollatzResearch.WordTrace tailWord_529518 prefixEnd_529518 271897249207564492089797 := by
  unfold tailWord_529518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414138511956774414956651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12875405397102796879768805 2414138511956774414956651)
  ·
    refine ⟨3621207767935161622434977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2414138511956774414956651 3621207767935161622434977)
    ·
      refine ⟨2715905825951371216826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3621207767935161622434977 2715905825951371216826233)
      ·
        refine ⟨2036929369463528412619675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2715905825951371216826233 2036929369463528412619675)
        ·
          refine ⟨3055394054195292618929513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036929369463528412619675 3055394054195292618929513)
          ·
            refine ⟨2291545540646469464197135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055394054195292618929513 2291545540646469464197135)
            ·
              refine ⟨3437318310969704196295703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291545540646469464197135 3437318310969704196295703)
              ·
                refine ⟨5155977466454556294443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437318310969704196295703 5155977466454556294443555)
                ·
                  refine ⟨7733966199681834441665333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155977466454556294443555 7733966199681834441665333)
                  ·
                    refine ⟨725059331220171978906125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733966199681834441665333 725059331220171978906125)
                    ·
                      refine ⟨271897249207564492089797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725059331220171978906125 271897249207564492089797)
                      ·
                        rfl

theorem cell23_529518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_529518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529518 prefixEnd_529518 := by exact prefixLift 529518
  have htrace : WordTrace (prefixWord ++ tailWord_529518) baseStart_529518 baseEnd_529518 := by
    simpa [prefixWord, tailWord_529518, baseEnd_529518] using wordTrace_append hprefix tailTrace_529518
  have hstable : (prefixWord ++ tailWord_529518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529518).length < 2 ^ (prefixWord ++ tailWord_529518).sum := by decide
  have hdescent : baseEnd_529518 < baseStart_529518 := by decide
  rcases family_descends (prefixWord ++ tailWord_529518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529525 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 7]
def baseStart_529525 : Nat := 118140960795 + 529525 * 2 ^ 59
def prefixEnd_529525 : Nat := 4983230072969 + 3 ^ 40 * 529525 * 2
def baseEnd_529525 : Nat := 30211204841349551633585

theorem tailTrace_529525 : CollatzResearch.WordTrace tailWord_529525 prefixEnd_529525 30211204841349551633585 := by
  unfold tailWord_529525
  simp only [CollatzResearch.WordTrace]
  refine ⟨19313363406628835515158029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12875575604419223676772019 19313363406628835515158029)
  ·
    refine ⟨7242511277485813318184261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19313363406628835515158029 7242511277485813318184261)
    ·
      refine ⟨1357970864528589997159549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7242511277485813318184261 1357970864528589997159549)
      ·
        refine ⟨509239074198221248934831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1357970864528589997159549 509239074198221248934831)
        ·
          refine ⟨763858611297331873402247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509239074198221248934831 763858611297331873402247)
          ·
            refine ⟨1145787916945997810103371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763858611297331873402247 1145787916945997810103371)
            ·
              refine ⟨1718681875418996715155057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145787916945997810103371 1718681875418996715155057)
              ·
                refine ⟨1289011406564247536366293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718681875418996715155057 1289011406564247536366293)
                ·
                  refine ⟨30211204841349551633585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1289011406564247536366293 30211204841349551633585)
                  ·
                    rfl

theorem cell23_529525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 7].length) (baseStart_529525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529525 prefixEnd_529525 := by exact prefixLift 529525
  have htrace : WordTrace (prefixWord ++ tailWord_529525) baseStart_529525 baseEnd_529525 := by
    simpa [prefixWord, tailWord_529525, baseEnd_529525] using wordTrace_append hprefix tailTrace_529525
  have hstable : (prefixWord ++ tailWord_529525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529525).length < 2 ^ (prefixWord ++ tailWord_529525).sum := by decide
  have hdescent : baseEnd_529525 < baseStart_529525 := by decide
  rcases family_descends (prefixWord ++ tailWord_529525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529585 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_529585 : Nat := 118140960795 + 529585 * 2 ^ 59
def prefixEnd_529585 : Nat := 4983230072969 + 3 ^ 40 * 529585 * 2
def baseEnd_529585 : Nat := 90643884137138576650663

theorem tailTrace_529585 : CollatzResearch.WordTrace tailWord_529585 prefixEnd_529585 90643884137138576650663 := by
  unfold tailWord_529585
  simp only [CollatzResearch.WordTrace]
  refine ⟨19315551786411465762342209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12877034524274310508228139 19315551786411465762342209)
  ·
    refine ⟨14486663839808599321756657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19315551786411465762342209 14486663839808599321756657)
    ·
      refine ⟨10864997879856449491317493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14486663839808599321756657 10864997879856449491317493)
      ·
        refine ⟨1018593551236542139811015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10864997879856449491317493 1018593551236542139811015)
        ·
          refine ⟨1527890326854813209716523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018593551236542139811015 1527890326854813209716523)
          ·
            refine ⟨2291835490282219814574785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527890326854813209716523 2291835490282219814574785)
            ·
              refine ⟨1718876617711664860931089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2291835490282219814574785 1718876617711664860931089)
              ·
                refine ⟨1289157463283748645698317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1718876617711664860931089 1289157463283748645698317)
                ·
                  refine ⟨483434048731405742136869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1289157463283748645698317 483434048731405742136869)
                  ·
                    refine ⟨90643884137138576650663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483434048731405742136869 90643884137138576650663)
                    ·
                      rfl

theorem cell23_529585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_529585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529585 prefixEnd_529585 := by exact prefixLift 529585
  have htrace : WordTrace (prefixWord ++ tailWord_529585) baseStart_529585 baseEnd_529585 := by
    simpa [prefixWord, tailWord_529585, baseEnd_529585] using wordTrace_append hprefix tailTrace_529585
  have hstable : (prefixWord ++ tailWord_529585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529585).length < 2 ^ (prefixWord ++ tailWord_529585).sum := by decide
  have hdescent : baseEnd_529585 < baseStart_529585 := by decide
  rcases family_descends (prefixWord ++ tailWord_529585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529598 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_529598 : Nat := 118140960795 + 529598 * 2 ^ 59
def prefixEnd_529598 : Nat := 4983230072969 + 3 ^ 40 * 529598 * 2
def baseEnd_529598 : Nat := 30215369739991575454381

theorem tailTrace_529598 : CollatzResearch.WordTrace tailWord_529598 prefixEnd_529598 30215369739991575454381 := by
  unfold tailWord_529598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414503241920546122820681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12877350623576245988376965 2414503241920546122820681)
  ·
    refine ⟨1810877431440409592115511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2414503241920546122820681 1810877431440409592115511)
    ·
      refine ⟨2716316147160614388173267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810877431440409592115511 2716316147160614388173267)
      ·
        refine ⟨4074474220740921582259901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716316147160614388173267 4074474220740921582259901)
        ·
          refine ⟨1527927832777845593347463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4074474220740921582259901 1527927832777845593347463)
          ·
            refine ⟨2291891749166768390021195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527927832777845593347463 2291891749166768390021195)
            ·
              refine ⟨3437837623750152585031793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2291891749166768390021195 3437837623750152585031793)
              ·
                refine ⟨2578378217812614438773845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437837623750152585031793 2578378217812614438773845)
                ·
                  refine ⟨30215369739991575454381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2578378217812614438773845 30215369739991575454381)
                  ·
                    rfl

theorem cell23_529598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_529598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529598 prefixEnd_529598 := by exact prefixLift 529598
  have htrace : WordTrace (prefixWord ++ tailWord_529598) baseStart_529598 baseEnd_529598 := by
    simpa [prefixWord, tailWord_529598, baseEnd_529598] using wordTrace_append hprefix tailTrace_529598
  have hstable : (prefixWord ++ tailWord_529598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529598).length < 2 ^ (prefixWord ++ tailWord_529598).sum := by decide
  have hdescent : baseEnd_529598 < baseStart_529598 := by decide
  rcases family_descends (prefixWord ++ tailWord_529598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529645 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_529645 : Nat := 118140960795 + 529645 * 2 ^ 59
def prefixEnd_529645 : Nat := 4983230072969 + 3 ^ 40 * 529645 * 2
def baseEnd_529645 : Nat := 90654153750228498400571

theorem tailTrace_529645 : CollatzResearch.WordTrace tailWord_529645 prefixEnd_529645 90654153750228498400571 := by
  unfold tailWord_529645
  simp only [CollatzResearch.WordTrace]
  refine ⟨19317740166194096009526389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12878493444129397339684259 19317740166194096009526389)
  ·
    refine ⟨1811038140580696500893099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19317740166194096009526389 1811038140580696500893099)
    ·
      refine ⟨2716557210871044751339649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811038140580696500893099 2716557210871044751339649)
      ·
        refine ⟨2037417908153283563504737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716557210871044751339649 2037417908153283563504737)
        ·
          refine ⟨1528063431114962672628553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2037417908153283563504737 1528063431114962672628553)
          ·
            refine ⟨1146047573336222004471415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1528063431114962672628553 1146047573336222004471415)
            ·
              refine ⟨1719071360004333006707123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146047573336222004471415 1719071360004333006707123)
              ·
                refine ⟨2578607040006499510060685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719071360004333006707123 2578607040006499510060685)
                ·
                  refine ⟨966977640002437316272757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2578607040006499510060685 966977640002437316272757)
                  ·
                    refine ⟨90654153750228498400571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 966977640002437316272757 90654153750228498400571)
                    ·
                      rfl

theorem cell23_529645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_529645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529645 prefixEnd_529645 := by exact prefixLift 529645
  have htrace : WordTrace (prefixWord ++ tailWord_529645) baseStart_529645 baseEnd_529645 := by
    simpa [prefixWord, tailWord_529645, baseEnd_529645] using wordTrace_append hprefix tailTrace_529645
  have hstable : (prefixWord ++ tailWord_529645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529645).length < 2 ^ (prefixWord ++ tailWord_529645).sum := by decide
  have hdescent : baseEnd_529645 < baseStart_529645 := by decide
  rcases family_descends (prefixWord ++ tailWord_529645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529658 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_529658 : Nat := 118140960795 + 529658 * 2 ^ 59
def prefixEnd_529658 : Nat := 4983230072969 + 3 ^ 40 * 529658 * 2
def baseEnd_529658 : Nat := 90656378833064648113051

theorem tailTrace_529658 : CollatzResearch.WordTrace tailWord_529658 prefixEnd_529658 90656378833064648113051 := by
  unfold tailWord_529658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829553578786749807437407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12878809543431332819833085 4829553578786749807437407)
  ·
    refine ⟨7244330368180124711156111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4829553578786749807437407 7244330368180124711156111)
    ·
      refine ⟨10866495552270187066734167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244330368180124711156111 10866495552270187066734167)
      ·
        refine ⟨16299743328405280600101251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10866495552270187066734167 16299743328405280600101251)
        ·
          refine ⟨24449614992607920900151877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16299743328405280600101251 24449614992607920900151877)
          ·
            refine ⟨4584302811113985168778477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24449614992607920900151877 4584302811113985168778477)
            ·
              refine ⟨1719113554167744438291929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4584302811113985168778477 1719113554167744438291929)
              ·
                refine ⟨1289335165625808328718947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719113554167744438291929 1289335165625808328718947)
                ·
                  refine ⟨1934002748438712493078421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289335165625808328718947 1934002748438712493078421)
                  ·
                    refine ⟨90656378833064648113051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1934002748438712493078421 90656378833064648113051)
                    ·
                      rfl

theorem cell23_529658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_529658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529658 prefixEnd_529658 := by exact prefixLift 529658
  have htrace : WordTrace (prefixWord ++ tailWord_529658) baseStart_529658 baseEnd_529658 := by
    simpa [prefixWord, tailWord_529658, baseEnd_529658] using wordTrace_append hprefix tailTrace_529658
  have hstable : (prefixWord ++ tailWord_529658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529658).length < 2 ^ (prefixWord ++ tailWord_529658).sum := by decide
  have hdescent : baseEnd_529658 < baseStart_529658 := by decide
  rcases family_descends (prefixWord ++ tailWord_529658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529671 : List Nat := [1, 1, 4, 17]
def baseStart_529671 : Nat := 118140960795 + 529671 * 2 ^ 59
def prefixEnd_529671 : Nat := 4983230072969 + 3 ^ 40 * 529671 * 2
def baseEnd_529671 : Nat := 124360224850344029939

theorem tailTrace_529671 : CollatzResearch.WordTrace tailWord_529671 prefixEnd_529671 124360224850344029939 := by
  unfold tailWord_529671
  simp only [CollatzResearch.WordTrace]
  refine ⟨19318688464099902449972867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12879125642733268299981911 19318688464099902449972867)
  ·
    refine ⟨28978032696149853674959301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19318688464099902449972867 28978032696149853674959301)
    ·
      refine ⟨5433381130528097564054869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28978032696149853674959301 5433381130528097564054869)
      ·
        refine ⟨124360224850344029939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 5433381130528097564054869 124360224850344029939)
        ·
          rfl

theorem cell23_529671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 17].length) (baseStart_529671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529671 prefixEnd_529671 := by exact prefixLift 529671
  have htrace : WordTrace (prefixWord ++ tailWord_529671) baseStart_529671 baseEnd_529671 := by
    simpa [prefixWord, tailWord_529671, baseEnd_529671] using wordTrace_append hprefix tailTrace_529671
  have hstable : (prefixWord ++ tailWord_529671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529671).length < 2 ^ (prefixWord ++ tailWord_529671).sum := by decide
  have hdescent : baseEnd_529671 < baseStart_529671 := by decide
  rcases family_descends (prefixWord ++ tailWord_529671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529675 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 2, 4]
def baseStart_529675 : Nat := 118140960795 + 529675 * 2 ^ 59
def prefixEnd_529675 : Nat := 4983230072969 + 3 ^ 40 * 529675 * 2
def baseEnd_529675 : Nat := 90659288556773459275525

theorem tailTrace_529675 : CollatzResearch.WordTrace tailWord_529675 prefixEnd_529675 90659288556773459275525 := by
  unfold tailWord_529675
  simp only [CollatzResearch.WordTrace]
  refine ⟨19318834356085411133118479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12879222904056940755412319 19318834356085411133118479)
  ·
    refine ⟨28978251534128116699677719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19318834356085411133118479 28978251534128116699677719)
    ·
      refine ⟨43467377301192175049516579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28978251534128116699677719 43467377301192175049516579)
      ·
        refine ⟨65201065951788262574274869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43467377301192175049516579 65201065951788262574274869)
        ·
          refine ⟨6112599932980149616338269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65201065951788262574274869 6112599932980149616338269)
          ·
            refine ⟨2292224974867556106126851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6112599932980149616338269 2292224974867556106126851)
            ·
              refine ⟨3438337462301334159190277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292224974867556106126851 3438337462301334159190277)
              ·
                refine ⟨644688274181500154848177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3438337462301334159190277 644688274181500154848177)
                ·
                  refine ⟨483516205636125116136133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644688274181500154848177 483516205636125116136133)
                  ·
                    refine ⟨90659288556773459275525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483516205636125116136133 90659288556773459275525)
                    ·
                      rfl

theorem cell23_529675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 4].length) (baseStart_529675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529675 prefixEnd_529675 := by exact prefixLift 529675
  have htrace : WordTrace (prefixWord ++ tailWord_529675) baseStart_529675 baseEnd_529675 := by
    simpa [prefixWord, tailWord_529675, baseEnd_529675] using wordTrace_append hprefix tailTrace_529675
  have hstable : (prefixWord ++ tailWord_529675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529675).length < 2 ^ (prefixWord ++ tailWord_529675).sum := by decide
  have hdescent : baseEnd_529675 < baseStart_529675 := by decide
  rcases family_descends (prefixWord ++ tailWord_529675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529676 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_529676 : Nat := 118140960795 + 529676 * 2 ^ 59
def prefixEnd_529676 : Nat := 4983230072969 + 3 ^ 40 * 529676 * 2
def baseEnd_529676 : Nat := 271978379150974873914071

theorem tailTrace_529676 : CollatzResearch.WordTrace tailWord_529676 prefixEnd_529676 271978379150974873914071 := by
  unfold tailWord_529676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659435414540894151952441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12879247219387858869269921 9659435414540894151952441)
  ·
    refine ⟨7244576560905670613964331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9659435414540894151952441 7244576560905670613964331)
    ·
      refine ⟨10866864841358505920946497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244576560905670613964331 10866864841358505920946497)
      ·
        refine ⟨8150148631018879440709873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10866864841358505920946497 8150148631018879440709873)
        ·
          refine ⟨6112611473264159580532405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8150148631018879440709873 6112611473264159580532405)
          ·
            refine ⟨573057325618514960674913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6112611473264159580532405 573057325618514960674913)
            ·
              refine ⟨429792994213886220506185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573057325618514960674913 429792994213886220506185)
              ·
                refine ⟨322344745660414665379639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429792994213886220506185 322344745660414665379639)
                ·
                  refine ⟨483517118490621998069459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322344745660414665379639 483517118490621998069459)
                  ·
                    refine ⟨725275677735932997104189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 483517118490621998069459 725275677735932997104189)
                    ·
                      refine ⟨271978379150974873914071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725275677735932997104189 271978379150974873914071)
                      ·
                        rfl

theorem cell23_529676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_529676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529676 prefixEnd_529676 := by exact prefixLift 529676
  have htrace : WordTrace (prefixWord ++ tailWord_529676) baseStart_529676 baseEnd_529676 := by
    simpa [prefixWord, tailWord_529676, baseEnd_529676] using wordTrace_append hprefix tailTrace_529676
  have hstable : (prefixWord ++ tailWord_529676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529676).length < 2 ^ (prefixWord ++ tailWord_529676).sum := by decide
  have hdescent : baseEnd_529676 < baseStart_529676 := by decide
  rcases family_descends (prefixWord ++ tailWord_529676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529688 : List Nat := [2, 1, 2, 3, 1, 3, 3, 8]
def baseStart_529688 : Nat := 118140960795 + 529688 * 2 ^ 59
def prefixEnd_529688 : Nat := 4983230072969 + 3 ^ 40 * 529688 * 2
def baseEnd_529688 : Nat := 10073501515512178776445

theorem tailTrace_529688 : CollatzResearch.WordTrace tailWord_529688 prefixEnd_529688 10073501515512178776445 := by
  unfold tailWord_529688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659654252519157176670859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12879539003358876235561145 9659654252519157176670859)
  ·
    refine ⟨14489481378778735765006289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9659654252519157176670859 14489481378778735765006289)
    ·
      refine ⟨10867111034084051823754717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14489481378778735765006289 10867111034084051823754717)
      ·
        refine ⟨4075166637781519433908019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10867111034084051823754717 4075166637781519433908019)
        ·
          refine ⟨6112749956672279150862029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075166637781519433908019 6112749956672279150862029)
          ·
            refine ⟨2292281233752104681573261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6112749956672279150862029 2292281233752104681573261)
            ·
              refine ⟨859605462657039255589973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2292281233752104681573261 859605462657039255589973)
              ·
                refine ⟨10073501515512178776445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 859605462657039255589973 10073501515512178776445)
                ·
                  rfl

theorem cell23_529688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 8].length) (baseStart_529688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529688 prefixEnd_529688 := by exact prefixLift 529688
  have htrace : WordTrace (prefixWord ++ tailWord_529688) baseStart_529688 baseEnd_529688 := by
    simpa [prefixWord, tailWord_529688, baseEnd_529688] using wordTrace_append hprefix tailTrace_529688
  have hstable : (prefixWord ++ tailWord_529688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529688).length < 2 ^ (prefixWord ++ tailWord_529688).sum := by decide
  have hdescent : baseEnd_529688 < baseStart_529688 := by decide
  rcases family_descends (prefixWord ++ tailWord_529688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529715 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3]
def baseStart_529715 : Nat := 118140960795 + 529715 * 2 ^ 59
def prefixEnd_529715 : Nat := 4983230072969 + 3 ^ 40 * 529715 * 2
def baseEnd_529715 : Nat := 271998404896500221326391

theorem tailTrace_529715 : CollatzResearch.WordTrace tailWord_529715 prefixEnd_529715 271998404896500221326391 := by
  unfold tailWord_529715
  simp only [CollatzResearch.WordTrace]
  refine ⟨19320293275940497964574599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12880195517293665309716399 19320293275940497964574599)
  ·
    refine ⟨28980439913910746946861899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19320293275940497964574599 28980439913910746946861899)
    ·
      refine ⟨43470659870866120420292849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28980439913910746946861899 43470659870866120420292849)
      ·
        refine ⟨32602994903149590315219637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43470659870866120420292849 32602994903149590315219637)
        ·
          refine ⟨3056530772170274092051841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32602994903149590315219637 3056530772170274092051841)
          ·
            refine ⟨2292398079127705569038881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3056530772170274092051841 2292398079127705569038881)
            ·
              refine ⟨1719298559345779176779161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292398079127705569038881 1719298559345779176779161)
              ·
                refine ⟨1289473919509334382584371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719298559345779176779161 1289473919509334382584371)
                ·
                  refine ⟨1934210879264001573876557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289473919509334382584371 1934210879264001573876557)
                  ·
                    refine ⟨725329079724000590203709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934210879264001573876557 725329079724000590203709)
                    ·
                      refine ⟨271998404896500221326391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725329079724000590203709 271998404896500221326391)
                      ·
                        rfl

theorem cell23_529715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_529715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529715 prefixEnd_529715 := by exact prefixLift 529715
  have htrace : WordTrace (prefixWord ++ tailWord_529715) baseStart_529715 baseEnd_529715 := by
    simpa [prefixWord, tailWord_529715, baseEnd_529715] using wordTrace_append hprefix tailTrace_529715
  have hstable : (prefixWord ++ tailWord_529715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529715).length < 2 ^ (prefixWord ++ tailWord_529715).sum := by decide
  have hdescent : baseEnd_529715 < baseStart_529715 := by decide
  rcases family_descends (prefixWord ++ tailWord_529715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529738 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_529738 : Nat := 118140960795 + 529738 * 2 ^ 59
def prefixEnd_529738 : Nat := 4983230072969 + 3 ^ 40 * 529738 * 2
def baseEnd_529738 : Nat := 272010214951553631338785

theorem tailTrace_529738 : CollatzResearch.WordTrace tailWord_529738 prefixEnd_529738 272010214951553631338785 := by
  unfold tailWord_529738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830283038714293223165467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12880754769904781928441245 4830283038714293223165467)
  ·
    refine ⟨7245424558071439834748201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830283038714293223165467 7245424558071439834748201)
    ·
      refine ⟨5434068418553579876061151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7245424558071439834748201 5434068418553579876061151)
      ·
        refine ⟨8151102627830369814091727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5434068418553579876061151 8151102627830369814091727)
        ·
          refine ⟨12226653941745554721137591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8151102627830369814091727 12226653941745554721137591)
          ·
            refine ⟨18339980912618332081706387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12226653941745554721137591 18339980912618332081706387)
            ·
              refine ⟨27509971368927498122559581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18339980912618332081706387 27509971368927498122559581)
              ·
                refine ⟨10316239263347811795959843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27509971368927498122559581 10316239263347811795959843)
                ·
                  refine ⟨15474358895021717693939765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10316239263347811795959843 15474358895021717693939765)
                  ·
                    refine ⟨1450721146408286033806853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15474358895021717693939765 1450721146408286033806853)
                    ·
                      refine ⟨272010214951553631338785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1450721146408286033806853 272010214951553631338785)
                      ·
                        rfl

theorem cell23_529738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_529738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529738 prefixEnd_529738 := by exact prefixLift 529738
  have htrace : WordTrace (prefixWord ++ tailWord_529738) baseStart_529738 baseEnd_529738 := by
    simpa [prefixWord, tailWord_529738, baseEnd_529738] using wordTrace_append hprefix tailTrace_529738
  have hstable : (prefixWord ++ tailWord_529738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529738).length < 2 ^ (prefixWord ++ tailWord_529738).sum := by decide
  have hdescent : baseEnd_529738 < baseStart_529738 := by decide
  rcases family_descends (prefixWord ++ tailWord_529738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529788 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_529788 : Nat := 118140960795 + 529788 * 2 ^ 59
def prefixEnd_529788 : Nat := 4983230072969 + 3 ^ 40 * 529788 * 2
def baseEnd_529788 : Nat := 272035888984278435713555

theorem tailTrace_529788 : CollatzResearch.WordTrace tailWord_529788 prefixEnd_529788 272035888984278435713555 := by
  unfold tailWord_529788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661477902338015715991009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12881970536450687621321345 9661477902338015715991009)
  ·
    refine ⟨7246108426753511786993257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9661477902338015715991009 7246108426753511786993257)
    ·
      refine ⟨5434581320065133840244943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7246108426753511786993257 5434581320065133840244943)
      ·
        refine ⟨8151871980097700760367415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5434581320065133840244943 8151871980097700760367415)
        ·
          refine ⟨12227807970146551140551123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8151871980097700760367415 12227807970146551140551123)
          ·
            refine ⟨18341711955219826710826685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12227807970146551140551123 18341711955219826710826685)
            ·
              refine ⟨6878141983207435016560007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18341711955219826710826685 6878141983207435016560007)
              ·
                refine ⟨10317212974811152524840011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878141983207435016560007 10317212974811152524840011)
                ·
                  refine ⟨15475819462216728787260017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317212974811152524840011 15475819462216728787260017)
                  ·
                    refine ⟨11606864596662546590445013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15475819462216728787260017 11606864596662546590445013)
                    ·
                      refine ⟨272035888984278435713555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11606864596662546590445013 272035888984278435713555)
                      ·
                        rfl

theorem cell23_529788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_529788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529788 prefixEnd_529788 := by exact prefixLift 529788
  have htrace : WordTrace (prefixWord ++ tailWord_529788) baseStart_529788 baseEnd_529788 := by
    simpa [prefixWord, tailWord_529788, baseEnd_529788] using wordTrace_append hprefix tailTrace_529788
  have hstable : (prefixWord ++ tailWord_529788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529788).length < 2 ^ (prefixWord ++ tailWord_529788).sum := by decide
  have hdescent : baseEnd_529788 < baseStart_529788 := by decide
  rcases family_descends (prefixWord ++ tailWord_529788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529789 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 2, 2, 2]
def baseStart_529789 : Nat := 118140960795 + 529789 * 2 ^ 59
def prefixEnd_529789 : Nat := 4983230072969 + 3 ^ 40 * 529789 * 2
def baseEnd_529789 : Nat := 272036402464932931801051

theorem tailTrace_529789 : CollatzResearch.WordTrace tailWord_529789 prefixEnd_529789 272036402464932931801051 := by
  unfold tailWord_529789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19322992277672408602768421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12881994851781605735178947 19322992277672408602768421)
  ·
    refine ⟨3623061052063576613019079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19322992277672408602768421 3623061052063576613019079)
    ·
      refine ⟨5434591578095364919528619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623061052063576613019079 5434591578095364919528619)
      ·
        refine ⟨8151887367143047379292929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5434591578095364919528619 8151887367143047379292929)
        ·
          refine ⟨6113915525357285534469697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8151887367143047379292929 6113915525357285534469697)
          ·
            refine ⟨4585436644017964150852273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113915525357285534469697 4585436644017964150852273)
            ·
              refine ⟨3439077483013473113139205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4585436644017964150852273 3439077483013473113139205)
              ·
                refine ⟨644827028065026208713601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3439077483013473113139205 644827028065026208713601)
                ·
                  refine ⟨483620271048769656535201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644827028065026208713601 483620271048769656535201)
                  ·
                    refine ⟨362715203286577242401401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483620271048769656535201 362715203286577242401401)
                    ·
                      refine ⟨272036402464932931801051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362715203286577242401401 272036402464932931801051)
                      ·
                        rfl

theorem cell23_529789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_529789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529789 prefixEnd_529789 := by exact prefixLift 529789
  have htrace : WordTrace (prefixWord ++ tailWord_529789) baseStart_529789 baseEnd_529789 := by
    simpa [prefixWord, tailWord_529789, baseEnd_529789] using wordTrace_append hprefix tailTrace_529789
  have hstable : (prefixWord ++ tailWord_529789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529789).length < 2 ^ (prefixWord ++ tailWord_529789).sum := by decide
  have hdescent : baseEnd_529789 < baseStart_529789 := by decide
  rcases family_descends (prefixWord ++ tailWord_529789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529795 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 7]
def baseStart_529795 : Nat := 118140960795 + 529795 * 2 ^ 59
def prefixEnd_529795 : Nat := 4983230072969 + 3 ^ 40 * 529795 * 2
def baseEnd_529795 : Nat := 30226609260984434258447

theorem tailTrace_529795 : CollatzResearch.WordTrace tailWord_529795 prefixEnd_529795 30226609260984434258447 := by
  unfold tailWord_529795
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323211115650671627486839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12882140743767114418324559 19323211115650671627486839)
  ·
    refine ⟨28984816673476007441230259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19323211115650671627486839 28984816673476007441230259)
    ·
      refine ⟨43477225010214011161845389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28984816673476007441230259 43477225010214011161845389)
      ·
        refine ⟨16303959378830254185692021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43477225010214011161845389 16303959378830254185692021)
        ·
          refine ⟨1528496191765336329908627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16303959378830254185692021 1528496191765336329908627)
          ·
            refine ⟨2292744287648004494862941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528496191765336329908627 2292744287648004494862941)
            ·
              refine ⟨859779107868001685573603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2292744287648004494862941 859779107868001685573603)
              ·
                refine ⟨1289668661802002528360405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859779107868001685573603 1289668661802002528360405)
                ·
                  refine ⟨30226609260984434258447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1289668661802002528360405 30226609260984434258447)
                  ·
                    rfl

theorem cell23_529795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 7].length) (baseStart_529795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529795 prefixEnd_529795 := by exact prefixLift 529795
  have htrace : WordTrace (prefixWord ++ tailWord_529795) baseStart_529795 baseEnd_529795 := by
    simpa [prefixWord, tailWord_529795, baseEnd_529795] using wordTrace_append hprefix tailTrace_529795
  have hstable : (prefixWord ++ tailWord_529795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529795).length < 2 ^ (prefixWord ++ tailWord_529795).sum := by decide
  have hdescent : baseEnd_529795 < baseStart_529795 := by decide
  rcases family_descends (prefixWord ++ tailWord_529795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529810 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_529810 : Nat := 118140960795 + 529810 * 2 ^ 59
def prefixEnd_529810 : Nat := 4983230072969 + 3 ^ 40 * 529810 * 2
def baseEnd_529810 : Nat := 272047185558677349638455

theorem tailTrace_529810 : CollatzResearch.WordTrace tailWord_529810 prefixEnd_529810 272047185558677349638455 := by
  unfold tailWord_529810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830939552649082297320721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12882505473730886126188589 4830939552649082297320721)
  ·
    refine ⟨3623204664486811722990541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4830939552649082297320721 3623204664486811722990541)
    ·
      refine ⟨1358701749182554396121453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3623204664486811722990541 1358701749182554396121453)
      ·
        refine ⟨509513155943457898545545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1358701749182554396121453 509513155943457898545545)
        ·
          refine ⟨382134866957593423909159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509513155943457898545545 382134866957593423909159)
          ·
            refine ⟨573202300436390135863739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382134866957593423909159 573202300436390135863739)
            ·
              refine ⟨859803450654585203795609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573202300436390135863739 859803450654585203795609)
              ·
                refine ⟨644852587990938902846707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859803450654585203795609 644852587990938902846707)
                ·
                  refine ⟨967278881986408354270061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 644852587990938902846707 967278881986408354270061)
                  ·
                    refine ⟨362729580744903132851273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967278881986408354270061 362729580744903132851273)
                    ·
                      refine ⟨272047185558677349638455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362729580744903132851273 272047185558677349638455)
                      ·
                        rfl

theorem cell23_529810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_529810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529810 prefixEnd_529810 := by exact prefixLift 529810
  have htrace : WordTrace (prefixWord ++ tailWord_529810) baseStart_529810 baseEnd_529810 := by
    simpa [prefixWord, tailWord_529810, baseEnd_529810] using wordTrace_append hprefix tailTrace_529810
  have hstable : (prefixWord ++ tailWord_529810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529810).length < 2 ^ (prefixWord ++ tailWord_529810).sum := by decide
  have hdescent : baseEnd_529810 < baseStart_529810 := by decide
  rcases family_descends (prefixWord ++ tailWord_529810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529855 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 7, 4]
def baseStart_529855 : Nat := 118140960795 + 529855 * 2 ^ 59
def prefixEnd_529855 : Nat := 4983230072969 + 3 ^ 40 * 529855 * 2
def baseEnd_529855 : Nat := 90690097396043224525249

theorem tailTrace_529855 : CollatzResearch.WordTrace tailWord_529855 prefixEnd_529855 90690097396043224525249 := by
  unfold tailWord_529855
  simp only [CollatzResearch.WordTrace]
  refine ⟨19325399495433301874671019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12883599663622201249780679 19325399495433301874671019)
  ·
    refine ⟨28988099243149952812006529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19325399495433301874671019 28988099243149952812006529)
    ·
      refine ⟨21741074432362464609004897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28988099243149952812006529 21741074432362464609004897)
      ·
        refine ⟨16305805824271848456753673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21741074432362464609004897 16305805824271848456753673)
        ·
          refine ⟨12229354368203886342565255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16305805824271848456753673 12229354368203886342565255)
          ·
            refine ⟨18344031552305829513847883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229354368203886342565255 18344031552305829513847883)
            ·
              refine ⟨27516047328458744270771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18344031552305829513847883 27516047328458744270771825)
              ·
                refine ⟨20637035496344058203078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27516047328458744270771825 20637035496344058203078869)
                ·
                  refine ⟨483680519445563864134661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20637035496344058203078869 483680519445563864134661)
                  ·
                    refine ⟨90690097396043224525249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483680519445563864134661 90690097396043224525249)
                    ·
                      rfl

theorem cell23_529855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_529855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529855 prefixEnd_529855 := by exact prefixLift 529855
  have htrace : WordTrace (prefixWord ++ tailWord_529855) baseStart_529855 baseEnd_529855 := by
    simpa [prefixWord, tailWord_529855, baseEnd_529855] using wordTrace_append hprefix tailTrace_529855
  have hstable : (prefixWord ++ tailWord_529855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529855).length < 2 ^ (prefixWord ++ tailWord_529855).sum := by decide
  have hdescent : baseEnd_529855 < baseStart_529855 := by decide
  rcases family_descends (prefixWord ++ tailWord_529855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529865 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_529865 : Nat := 118140960795 + 529865 * 2 ^ 59
def prefixEnd_529865 : Nat := 4983230072969 + 3 ^ 40 * 529865 * 2
def baseEnd_529865 : Nat := 272075426994674634450701

theorem tailTrace_529865 : CollatzResearch.WordTrace tailWord_529865 prefixEnd_529865 272075426994674634450701 := by
  unfold tailWord_529865
  simp only [CollatzResearch.WordTrace]
  refine ⟨19325764225397073582535049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12883842816931382388356699 19325764225397073582535049)
  ·
    refine ⟨14494323169047805186901287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19325764225397073582535049 14494323169047805186901287)
    ·
      refine ⟨21741484753571707780351931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14494323169047805186901287 21741484753571707780351931)
      ·
        refine ⟨32612227130357561670527897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21741484753571707780351931 32612227130357561670527897)
        ·
          refine ⟨24459170347768171252895923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32612227130357561670527897 24459170347768171252895923)
          ·
            refine ⟨36688755521652256879343885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24459170347768171252895923 36688755521652256879343885)
            ·
              refine ⟨13758283320619596329753957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36688755521652256879343885 13758283320619596329753957)
              ·
                refine ⟨2579678122616174311828867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13758283320619596329753957 2579678122616174311828867)
                ·
                  refine ⟨3869517183924261467743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579678122616174311828867 3869517183924261467743301)
                  ·
                    refine ⟨725534471985799025201869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869517183924261467743301 725534471985799025201869)
                    ·
                      refine ⟨272075426994674634450701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725534471985799025201869 272075426994674634450701)
                      ·
                        rfl

theorem cell23_529865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_529865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529865 prefixEnd_529865 := by exact prefixLift 529865
  have htrace : WordTrace (prefixWord ++ tailWord_529865) baseStart_529865 baseEnd_529865 := by
    simpa [prefixWord, tailWord_529865, baseEnd_529865] using wordTrace_append hprefix tailTrace_529865
  have hstable : (prefixWord ++ tailWord_529865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529865).length < 2 ^ (prefixWord ++ tailWord_529865).sum := by decide
  have hdescent : baseEnd_529865 < baseStart_529865 := by decide
  rcases family_descends (prefixWord ++ tailWord_529865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529876 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_529876 : Nat := 118140960795 + 529876 * 2 ^ 59
def prefixEnd_529876 : Nat := 4983230072969 + 3 ^ 40 * 529876 * 2
def baseEnd_529876 : Nat := 90693691760624697137717

theorem tailTrace_529876 : CollatzResearch.WordTrace tailWord_529876 prefixEnd_529876 90693691760624697137717 := by
  unfold tailWord_529876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663082714178611230592741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12884110285571481640790321 9663082714178611230592741)
  ·
    refine ⟨1811828008908489605736139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9663082714178611230592741 1811828008908489605736139)
    ·
      refine ⟨2717742013362734408604209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811828008908489605736139 2717742013362734408604209)
      ·
        refine ⟨2038306510022050806453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2717742013362734408604209 2038306510022050806453157)
        ·
          refine ⟨382182470629134526209967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2038306510022050806453157 382182470629134526209967)
          ·
            refine ⟨573273705943701789314951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382182470629134526209967 573273705943701789314951)
            ·
              refine ⟨859910558915552683972427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573273705943701789314951 859910558915552683972427)
              ·
                refine ⟨1289865838373329025958641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859910558915552683972427 1289865838373329025958641)
                ·
                  refine ⟨967399378779996769468981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289865838373329025958641 967399378779996769468981)
                  ·
                    refine ⟨90693691760624697137717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 967399378779996769468981 90693691760624697137717)
                    ·
                      rfl

theorem cell23_529876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_529876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529876 prefixEnd_529876 := by exact prefixLift 529876
  have htrace : WordTrace (prefixWord ++ tailWord_529876) baseStart_529876 baseEnd_529876 := by
    simpa [prefixWord, tailWord_529876, baseEnd_529876] using wordTrace_append hprefix tailTrace_529876
  have hstable : (prefixWord ++ tailWord_529876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529876).length < 2 ^ (prefixWord ++ tailWord_529876).sum := by decide
  have hdescent : baseEnd_529876 < baseStart_529876 := by decide
  rcases family_descends (prefixWord ++ tailWord_529876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529882 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_529882 : Nat := 118140960795 + 529882 * 2 ^ 59
def prefixEnd_529882 : Nat := 4983230072969 + 3 ^ 40 * 529882 * 2
def baseEnd_529882 : Nat := 272084156165801067938123

theorem tailTrace_529882 : CollatzResearch.WordTrace tailWord_529882 prefixEnd_529882 272084156165801067938123 := by
  unfold tailWord_529882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831596066583871371475975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12884256177556990323935933 4831596066583871371475975)
  ·
    refine ⟨7247394099875807057213963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831596066583871371475975 7247394099875807057213963)
    ·
      refine ⟨10871091149813710585820945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7247394099875807057213963 10871091149813710585820945)
      ·
        refine ⟨8153318362360282939365709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10871091149813710585820945 8153318362360282939365709)
        ·
          refine ⟨3057494385885106102262141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8153318362360282939365709 3057494385885106102262141)
          ·
            refine ⟨1146560394706914788348303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3057494385885106102262141 1146560394706914788348303)
            ·
              refine ⟨1719840592060372182522455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146560394706914788348303 1719840592060372182522455)
              ·
                refine ⟨2579760888090558273783683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719840592060372182522455 2579760888090558273783683)
                ·
                  refine ⟨3869641332135837410675525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579760888090558273783683 3869641332135837410675525)
                  ·
                    refine ⟨725557749775469514501661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869641332135837410675525 725557749775469514501661)
                    ·
                      refine ⟨272084156165801067938123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725557749775469514501661 272084156165801067938123)
                      ·
                        rfl

theorem cell23_529882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_529882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529882 prefixEnd_529882 := by exact prefixLift 529882
  have htrace : WordTrace (prefixWord ++ tailWord_529882) baseStart_529882 baseEnd_529882 := by
    simpa [prefixWord, tailWord_529882, baseEnd_529882] using wordTrace_append hprefix tailTrace_529882
  have hstable : (prefixWord ++ tailWord_529882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529882).length < 2 ^ (prefixWord ++ tailWord_529882).sum := by decide
  have hdescent : baseEnd_529882 < baseStart_529882 := by decide
  rcases family_descends (prefixWord ++ tailWord_529882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529889 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 1, 4]
def baseStart_529889 : Nat := 118140960795 + 529889 * 2 ^ 59
def prefixEnd_529889 : Nat := 4983230072969 + 3 ^ 40 * 529889 * 2
def baseEnd_529889 : Nat := 90695916843460846850197

theorem tailTrace_529889 : CollatzResearch.WordTrace tailWord_529889 prefixEnd_529889 90695916843460846850197 := by
  unfold tailWord_529889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19326639577310125681408721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12884426384873417120939147 19326639577310125681408721)
  ·
    refine ⟨14494979682982594261056541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19326639577310125681408721 14494979682982594261056541)
    ·
      refine ⟨5435617381118472847896203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14494979682982594261056541 5435617381118472847896203)
      ·
        refine ⟨8153426071677709271844305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5435617381118472847896203 8153426071677709271844305)
        ·
          refine ⟨6115069553758281953883229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8153426071677709271844305 6115069553758281953883229)
          ·
            refine ⟨2293151082659355732706211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6115069553758281953883229 2293151082659355732706211)
            ·
              refine ⟨3439726623989033599059317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293151082659355732706211 3439726623989033599059317)
              ·
                refine ⟨322474370998971899911811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3439726623989033599059317 322474370998971899911811)
                ·
                  refine ⟨483711556498457849867717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322474370998971899911811 483711556498457849867717)
                  ·
                    refine ⟨90695916843460846850197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483711556498457849867717 90695916843460846850197)
                    ·
                      rfl

theorem cell23_529889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_529889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529889 prefixEnd_529889 := by exact prefixLift 529889
  have htrace : WordTrace (prefixWord ++ tailWord_529889) baseStart_529889 baseEnd_529889 := by
    simpa [prefixWord, tailWord_529889, baseEnd_529889] using wordTrace_append hprefix tailTrace_529889
  have hstable : (prefixWord ++ tailWord_529889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529889).length < 2 ^ (prefixWord ++ tailWord_529889).sum := by decide
  have hdescent : baseEnd_529889 < baseStart_529889 := by decide
  rcases family_descends (prefixWord ++ tailWord_529889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529905 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_529905 : Nat := 118140960795 + 529905 * 2 ^ 59
def prefixEnd_529905 : Nat := 4983230072969 + 3 ^ 40 * 529905 * 2
def baseEnd_529905 : Nat := 272095966220854477950517

theorem tailTrace_529905 : CollatzResearch.WordTrace tailWord_529905 prefixEnd_529905 272095966220854477950517 := by
  unfold tailWord_529905
  simp only [CollatzResearch.WordTrace]
  refine ⟨19327223145252160413991169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12884815430168106942660779 19327223145252160413991169)
  ·
    refine ⟨14495417358939120310493377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19327223145252160413991169 14495417358939120310493377)
    ·
      refine ⟨10871563019204340232870033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14495417358939120310493377 10871563019204340232870033)
      ·
        refine ⟨8153672264403255174652525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10871563019204340232870033 8153672264403255174652525)
        ·
          refine ⟨3057627099151220690494697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8153672264403255174652525 3057627099151220690494697)
          ·
            refine ⟨2293220324363415517871023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057627099151220690494697 2293220324363415517871023)
            ·
              refine ⟨3439830486545123276806535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293220324363415517871023 3439830486545123276806535)
              ·
                refine ⟨5159745729817684915209803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439830486545123276806535 5159745729817684915209803)
                ·
                  refine ⟨7739618594726527372814705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159745729817684915209803 7739618594726527372814705)
                  ·
                    refine ⟨5804713946044895529611029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7739618594726527372814705 5804713946044895529611029)
                    ·
                      refine ⟨272095966220854477950517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5804713946044895529611029 272095966220854477950517)
                      ·
                        rfl

theorem cell23_529905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_529905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529905 prefixEnd_529905 := by exact prefixLift 529905
  have htrace : WordTrace (prefixWord ++ tailWord_529905) baseStart_529905 baseEnd_529905 := by
    simpa [prefixWord, tailWord_529905, baseEnd_529905] using wordTrace_append hprefix tailTrace_529905
  have hstable : (prefixWord ++ tailWord_529905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529905).length < 2 ^ (prefixWord ++ tailWord_529905).sum := by decide
  have hdescent : baseEnd_529905 < baseStart_529905 := by decide
  rcases family_descends (prefixWord ++ tailWord_529905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529906 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_529906 : Nat := 118140960795 + 529906 * 2 ^ 59
def prefixEnd_529906 : Nat := 4983230072969 + 3 ^ 40 * 529906 * 2
def baseEnd_529906 : Nat := 90698826567169658012671

theorem tailTrace_529906 : CollatzResearch.WordTrace tailWord_529906 prefixEnd_529906 90698826567169658012671 := by
  unfold tailWord_529906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831814904562134396194393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12884839745499025056518381 4831814904562134396194393)
  ·
    refine ⟨3623861178421600797145795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4831814904562134396194393 3623861178421600797145795)
    ·
      refine ⟨5435791767632401195718693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623861178421600797145795 5435791767632401195718693)
      ·
        refine ⟨1019210956431075224197255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5435791767632401195718693 1019210956431075224197255)
        ·
          refine ⟨1528816434646612836295883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019210956431075224197255 1528816434646612836295883)
          ·
            refine ⟨2293224651969919254443825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528816434646612836295883 2293224651969919254443825)
            ·
              refine ⟨1719918488977439440832869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293224651969919254443825 1719918488977439440832869)
              ·
                refine ⟨322484716683269895156163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1719918488977439440832869 322484716683269895156163)
                ·
                  refine ⟨483727075024904842734245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322484716683269895156163 483727075024904842734245)
                  ·
                    refine ⟨90698826567169658012671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483727075024904842734245 90698826567169658012671)
                    ·
                      rfl

theorem cell23_529906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_529906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529906 prefixEnd_529906 := by exact prefixLift 529906
  have htrace : WordTrace (prefixWord ++ tailWord_529906) baseStart_529906 baseEnd_529906 := by
    simpa [prefixWord, tailWord_529906, baseEnd_529906] using wordTrace_append hprefix tailTrace_529906
  have hstable : (prefixWord ++ tailWord_529906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529906).length < 2 ^ (prefixWord ++ tailWord_529906).sum := by decide
  have hdescent : baseEnd_529906 < baseStart_529906 := by decide
  rcases family_descends (prefixWord ++ tailWord_529906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529940 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_529940 : Nat := 118140960795 + 529940 * 2 ^ 59
def prefixEnd_529940 : Nat := 4983230072969 + 3 ^ 40 * 529940 * 2
def baseEnd_529940 : Nat := 90704646014587280337619

theorem tailTrace_529940 : CollatzResearch.WordTrace tailWord_529940 prefixEnd_529940 90704646014587280337619 := by
  unfold tailWord_529940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664249850062680695757637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12885666466750240927676849 9664249850062680695757637)
  ·
    refine ⟨1812046846886752630454557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9664249850062680695757637 1812046846886752630454557)
    ·
      refine ⟨679517567582532236420459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1812046846886752630454557 679517567582532236420459)
      ·
        refine ⟨1019276351373798354630689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679517567582532236420459 1019276351373798354630689)
        ·
          refine ⟨764457263530348765973017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019276351373798354630689 764457263530348765973017)
          ·
            refine ⟨573342947647761574479763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764457263530348765973017 573342947647761574479763)
            ·
              refine ⟨860014421471642361719645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573342947647761574479763 860014421471642361719645)
              ·
                refine ⟨322505408051865885644867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860014421471642361719645 322505408051865885644867)
                ·
                  refine ⟨483758112077798828467301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322505408051865885644867 483758112077798828467301)
                  ·
                    refine ⟨90704646014587280337619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483758112077798828467301 90704646014587280337619)
                    ·
                      rfl

theorem cell23_529940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_529940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529940 prefixEnd_529940 := by exact prefixLift 529940
  have htrace : WordTrace (prefixWord ++ tailWord_529940) baseStart_529940 baseEnd_529940 := by
    simpa [prefixWord, tailWord_529940, baseEnd_529940] using wordTrace_append hprefix tailTrace_529940
  have hstable : (prefixWord ++ tailWord_529940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529940).length < 2 ^ (prefixWord ++ tailWord_529940).sum := by decide
  have hdescent : baseEnd_529940 < baseStart_529940 := by decide
  rcases family_descends (prefixWord ++ tailWord_529940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529950 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_529950 : Nat := 118140960795 + 529950 * 2 ^ 59
def prefixEnd_529950 : Nat := 4983230072969 + 3 ^ 40 * 529950 * 2
def baseEnd_529950 : Nat := 272119072850306801887811

theorem tailTrace_529950 : CollatzResearch.WordTrace tailWord_529950 prefixEnd_529950 272119072850306801887811 := by
  unfold tailWord_529950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416108053761141637422413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12885909620059422066252869 2416108053761141637422413)
  ·
    refine ⟨906040520160428114033405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2416108053761141637422413 906040520160428114033405)
    ·
      refine ⟨339765195060160542762527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 906040520160428114033405 339765195060160542762527)
      ·
        refine ⟨509647792590240814143791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339765195060160542762527 509647792590240814143791)
        ·
          refine ⟨764471688885361221215687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509647792590240814143791 764471688885361221215687)
          ·
            refine ⟨1146707533328041831823531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764471688885361221215687 1146707533328041831823531)
            ·
              refine ⟨1720061299992062747735297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146707533328041831823531 1720061299992062747735297)
              ·
                refine ⟨1290045974994047060801473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720061299992062747735297 1290045974994047060801473)
                ·
                  refine ⟨967534481245535295601105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290045974994047060801473 967534481245535295601105)
                  ·
                    refine ⟨725650860934151471700829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 967534481245535295601105 725650860934151471700829)
                    ·
                      refine ⟨272119072850306801887811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725650860934151471700829 272119072850306801887811)
                      ·
                        rfl

theorem cell23_529950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_529950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529950 prefixEnd_529950 := by exact prefixLift 529950
  have htrace : WordTrace (prefixWord ++ tailWord_529950) baseStart_529950 baseEnd_529950 := by
    simpa [prefixWord, tailWord_529950, baseEnd_529950] using wordTrace_append hprefix tailTrace_529950
  have hstable : (prefixWord ++ tailWord_529950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529950).length < 2 ^ (prefixWord ++ tailWord_529950).sum := by decide
  have hdescent : baseEnd_529950 < baseStart_529950 := by decide
  rcases family_descends (prefixWord ++ tailWord_529950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529975 : List Nat := [1, 1, 3, 1, 2, 4, 1, 10]
def baseStart_529975 : Nat := 118140960795 + 529975 * 2 ^ 59
def prefixEnd_529975 : Nat := 4983230072969 + 3 ^ 40 * 529975 * 2
def baseEnd_529975 : Nat := 10078959624691452002785

theorem tailTrace_529975 : CollatzResearch.WordTrace tailWord_529975 prefixEnd_529975 10078959624691452002785 := by
  unfold tailWord_529975
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329776254998562369039379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12886517503332374912692919 19329776254998562369039379)
  ·
    refine ⟨28994664382497843553559069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19329776254998562369039379 28994664382497843553559069)
    ·
      refine ⟨10872999143436691332584651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28994664382497843553559069 10872999143436691332584651)
      ·
        refine ⟨16309498715155036998876977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10872999143436691332584651 16309498715155036998876977)
        ·
          refine ⟨12232124036366277749157733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16309498715155036998876977 12232124036366277749157733)
          ·
            refine ⟨2293523256818677077967075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12232124036366277749157733 2293523256818677077967075)
            ·
              refine ⟨3440284885228015616950613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293523256818677077967075 3440284885228015616950613)
              ·
                refine ⟨10078959624691452002785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3440284885228015616950613 10078959624691452002785)
                ·
                  rfl

theorem cell23_529975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 10].length) (baseStart_529975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529975 prefixEnd_529975 := by exact prefixLift 529975
  have htrace : WordTrace (prefixWord ++ tailWord_529975) baseStart_529975 baseEnd_529975 := by
    simpa [prefixWord, tailWord_529975, baseEnd_529975] using wordTrace_append hprefix tailTrace_529975
  have hstable : (prefixWord ++ tailWord_529975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529975).length < 2 ^ (prefixWord ++ tailWord_529975).sum := by decide
  have hdescent : baseEnd_529975 < baseStart_529975 := by decide
  rcases family_descends (prefixWord ++ tailWord_529975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_529990 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_529990 : Nat := 118140960795 + 529990 * 2 ^ 59
def prefixEnd_529990 : Nat := 4983230072969 + 3 ^ 40 * 529990 * 2
def baseEnd_529990 : Nat := 272139612076486645387627

theorem tailTrace_529990 : CollatzResearch.WordTrace tailWord_529990 prefixEnd_529990 272139612076486645387627 := by
  unfold tailWord_529990
  simp only [CollatzResearch.WordTrace]
  refine ⟨604072604685756872838607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12886882233296146620556949 604072604685756872838607)
  ·
    refine ⟨906108907028635309257911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604072604685756872838607 906108907028635309257911)
    ·
      refine ⟨1359163360542952963886867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906108907028635309257911 1359163360542952963886867)
      ·
        refine ⟨2038745040814429445830301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359163360542952963886867 2038745040814429445830301)
        ·
          refine ⟨764529390305411042186363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2038745040814429445830301 764529390305411042186363)
          ·
            refine ⟨1146794085458116563279545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764529390305411042186363 1146794085458116563279545)
            ·
              refine ⟨860095564093587422459659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146794085458116563279545 860095564093587422459659)
              ·
                refine ⟨1290143346140381133689489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860095564093587422459659 1290143346140381133689489)
                ·
                  refine ⟨967607509605285850267117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290143346140381133689489 967607509605285850267117)
                  ·
                    refine ⟨362852816101982193850169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 967607509605285850267117 362852816101982193850169)
                    ·
                      refine ⟨272139612076486645387627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362852816101982193850169 272139612076486645387627)
                      ·
                        rfl

theorem cell23_529990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_529990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_529990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_529990 prefixEnd_529990 := by exact prefixLift 529990
  have htrace : WordTrace (prefixWord ++ tailWord_529990) baseStart_529990 baseEnd_529990 := by
    simpa [prefixWord, tailWord_529990, baseEnd_529990] using wordTrace_append hprefix tailTrace_529990
  have hstable : (prefixWord ++ tailWord_529990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_529990).length < 2 ^ (prefixWord ++ tailWord_529990).sum := by decide
  have hdescent : baseEnd_529990 < baseStart_529990 := by decide
  rcases family_descends (prefixWord ++ tailWord_529990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530015 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_530015 : Nat := 118140960795 + 530015 * 2 ^ 59
def prefixEnd_530015 : Nat := 4983230072969 + 3 ^ 40 * 530015 * 2
def baseEnd_530015 : Nat := 272152449092849047575011

theorem tailTrace_530015 : CollatzResearch.WordTrace tailWord_530015 prefixEnd_530015 272152449092849047575011 := by
  unfold tailWord_530015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331235174853649200495499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12887490116569099466996999 19331235174853649200495499)
  ·
    refine ⟨28996852762280473800743249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19331235174853649200495499 28996852762280473800743249)
    ·
      refine ⟨21747639571710355350557437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28996852762280473800743249 21747639571710355350557437)
      ·
        refine ⟨8155364839391383256459039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21747639571710355350557437 8155364839391383256459039)
        ·
          refine ⟨12233047259087074884688559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8155364839391383256459039 12233047259087074884688559)
          ·
            refine ⟨18349570888630612327032839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233047259087074884688559 18349570888630612327032839)
            ·
              refine ⟨27524356332945918490549259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18349570888630612327032839 27524356332945918490549259)
              ·
                refine ⟨41286534499418877735823889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27524356332945918490549259 41286534499418877735823889)
                ·
                  refine ⟨30964900874564158301867917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41286534499418877735823889 30964900874564158301867917)
                  ·
                    refine ⟨11611837827961559363200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30964900874564158301867917 11611837827961559363200469)
                    ·
                      refine ⟨272152449092849047575011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11611837827961559363200469 272152449092849047575011)
                      ·
                        rfl

theorem cell23_530015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_530015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530015 prefixEnd_530015 := by exact prefixLift 530015
  have htrace : WordTrace (prefixWord ++ tailWord_530015) baseStart_530015 baseEnd_530015 := by
    simpa [prefixWord, tailWord_530015, baseEnd_530015] using wordTrace_append hprefix tailTrace_530015
  have hstable : (prefixWord ++ tailWord_530015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530015).length < 2 ^ (prefixWord ++ tailWord_530015).sum := by decide
  have hdescent : baseEnd_530015 < baseStart_530015 := by decide
  rcases family_descends (prefixWord ++ tailWord_530015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530020 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_530020 : Nat := 118140960795 + 530020 * 2 ^ 59
def prefixEnd_530020 : Nat := 4983230072969 + 3 ^ 40 * 530020 * 2
def baseEnd_530020 : Nat := 272155016496121528012489

theorem tailTrace_530020 : CollatzResearch.WordTrace tailWord_530020 prefixEnd_530020 272155016496121528012489 := by
  unfold tailWord_530020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9665708769917767527213757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12887611693223690036285009 9665708769917767527213757)
  ·
    refine ⟨3624640788719162822705159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9665708769917767527213757 3624640788719162822705159)
    ·
      refine ⟨5436961183078744234057739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3624640788719162822705159 5436961183078744234057739)
      ·
        refine ⟨8155441774618116351086609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436961183078744234057739 8155441774618116351086609)
        ·
          refine ⟨6116581330963587263314957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8155441774618116351086609 6116581330963587263314957)
          ·
            refine ⟨2293717999111345223743109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6116581330963587263314957 2293717999111345223743109)
            ·
              refine ⟨430072124833377229451833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2293717999111345223743109 430072124833377229451833)
              ·
                refine ⟨322554093625032922088875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430072124833377229451833 322554093625032922088875)
                ·
                  refine ⟨483831140437549383133313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322554093625032922088875 483831140437549383133313)
                  ·
                    refine ⟨362873355328162037349985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483831140437549383133313 362873355328162037349985)
                    ·
                      refine ⟨272155016496121528012489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362873355328162037349985 272155016496121528012489)
                      ·
                        rfl

theorem cell23_530020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_530020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530020 prefixEnd_530020 := by exact prefixLift 530020
  have htrace : WordTrace (prefixWord ++ tailWord_530020) baseStart_530020 baseEnd_530020 := by
    simpa [prefixWord, tailWord_530020, baseEnd_530020] using wordTrace_append hprefix tailTrace_530020
  have hstable : (prefixWord ++ tailWord_530020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530020).length < 2 ^ (prefixWord ++ tailWord_530020).sum := by decide
  have hdescent : baseEnd_530020 < baseStart_530020 := by decide
  rcases family_descends (prefixWord ++ tailWord_530020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530059 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 4, 2]
def baseStart_530059 : Nat := 118140960795 + 530059 * 2 ^ 59
def prefixEnd_530059 : Nat := 4983230072969 + 3 ^ 40 * 530059 * 2
def baseEnd_530059 : Nat := 272175042241646875424809

theorem tailTrace_530059 : CollatzResearch.WordTrace tailWord_530059 prefixEnd_530059 272175042241646875424809 := by
  unfold tailWord_530059
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332839986694244715097231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12888559991129496476731487 19332839986694244715097231)
  ·
    refine ⟨28999259980041367072645847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332839986694244715097231 28999259980041367072645847)
    ·
      refine ⟨43498889970062050608968771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28999259980041367072645847 43498889970062050608968771)
      ·
        refine ⟨65248334955093075913453157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43498889970062050608968771 65248334955093075913453157)
        ·
          refine ⟨12234062804079951733772467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65248334955093075913453157 12234062804079951733772467)
          ·
            refine ⟨18351094206119927600658701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12234062804079951733772467 18351094206119927600658701)
            ·
              refine ⟨6881660327294972850247013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18351094206119927600658701 6881660327294972850247013)
              ·
                refine ⟨1290311311367807409421315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6881660327294972850247013 1290311311367807409421315)
                ·
                  refine ⟨1935466967051711114131973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290311311367807409421315 1935466967051711114131973)
                  ·
                    refine ⟨362900056322195833899745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1935466967051711114131973 362900056322195833899745)
                    ·
                      refine ⟨272175042241646875424809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 362900056322195833899745 272175042241646875424809)
                      ·
                        rfl

theorem cell23_530059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4, 2].length) (baseStart_530059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530059 prefixEnd_530059 := by exact prefixLift 530059
  have htrace : WordTrace (prefixWord ++ tailWord_530059) baseStart_530059 baseEnd_530059 := by
    simpa [prefixWord, tailWord_530059, baseEnd_530059] using wordTrace_append hprefix tailTrace_530059
  have hstable : (prefixWord ++ tailWord_530059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530059).length < 2 ^ (prefixWord ++ tailWord_530059).sum := by decide
  have hdescent : baseEnd_530059 < baseStart_530059 := by decide
  rcases family_descends (prefixWord ++ tailWord_530059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530112 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_530112 : Nat := 118140960795 + 530112 * 2 ^ 59
def prefixEnd_530112 : Nat := 4983230072969 + 3 ^ 40 * 530112 * 2
def baseEnd_530112 : Nat := 90734085572111722687355

theorem tailTrace_530112 : CollatzResearch.WordTrace tailWord_530112 prefixEnd_530112 90734085572111722687355 := by
  unfold tailWord_530112
  simp only [CollatzResearch.WordTrace]
  refine ⟨9667386527751117383388295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12889848703668156511184393 9667386527751117383388295)
  ·
    refine ⟨14501079791626676075082443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9667386527751117383388295 14501079791626676075082443)
    ·
      refine ⟨21751619687440014112623665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14501079791626676075082443 21751619687440014112623665)
      ·
        refine ⟨16313714765580010584467749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21751619687440014112623665 16313714765580010584467749)
        ·
          refine ⟨3058821518546251984587703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16313714765580010584467749 3058821518546251984587703)
          ·
            refine ⟨4588232277819377976881555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058821518546251984587703 4588232277819377976881555)
            ·
              refine ⟨6882348416729066965322333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588232277819377976881555 6882348416729066965322333)
              ·
                refine ⟨2580880656273400111995875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6882348416729066965322333 2580880656273400111995875)
                ·
                  refine ⟨3871320984410100167993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580880656273400111995875 3871320984410100167993813)
                  ·
                    refine ⟨90734085572111722687355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3871320984410100167993813 90734085572111722687355)
                    ·
                      rfl

theorem cell23_530112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_530112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530112 prefixEnd_530112 := by exact prefixLift 530112
  have htrace : WordTrace (prefixWord ++ tailWord_530112) baseStart_530112 baseEnd_530112 := by
    simpa [prefixWord, tailWord_530112, baseEnd_530112] using wordTrace_append hprefix tailTrace_530112
  have hstable : (prefixWord ++ tailWord_530112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530112).length < 2 ^ (prefixWord ++ tailWord_530112).sum := by decide
  have hdescent : baseEnd_530112 < baseStart_530112 := by decide
  rcases family_descends (prefixWord ++ tailWord_530112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530129 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_530129 : Nat := 118140960795 + 530129 * 2 ^ 59
def prefixEnd_530129 : Nat := 4983230072969 + 3 ^ 40 * 530129 * 2
def baseEnd_530129 : Nat := 90736995295820533849829

theorem tailTrace_530129 : CollatzResearch.WordTrace tailWord_530129 prefixEnd_530129 90736995295820533849829 := by
  unfold tailWord_530129
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335393096440646670145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890262064293764446763627 19335393096440646670145441)
  ·
    refine ⟨14501544822330485002609081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19335393096440646670145441 14501544822330485002609081)
    ·
      refine ⟨10876158616747863751956811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14501544822330485002609081 10876158616747863751956811)
      ·
        refine ⟨16314237925121795627935217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10876158616747863751956811 16314237925121795627935217)
        ·
          refine ⟨12235678443841346720951413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16314237925121795627935217 12235678443841346720951413)
          ·
            refine ⟨1147094854110126255089195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12235678443841346720951413 1147094854110126255089195)
            ·
              refine ⟨1720642281165189382633793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147094854110126255089195 1720642281165189382633793)
              ·
                refine ⟨1290481710873892036975345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720642281165189382633793 1290481710873892036975345)
                ·
                  refine ⟨967861283155419027731509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290481710873892036975345 967861283155419027731509)
                  ·
                    refine ⟨90736995295820533849829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 967861283155419027731509 90736995295820533849829)
                    ·
                      rfl

theorem cell23_530129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_530129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530129 prefixEnd_530129 := by exact prefixLift 530129
  have htrace : WordTrace (prefixWord ++ tailWord_530129) baseStart_530129 baseEnd_530129 := by
    simpa [prefixWord, tailWord_530129, baseEnd_530129] using wordTrace_append hprefix tailTrace_530129
  have hstable : (prefixWord ++ tailWord_530129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530129).length < 2 ^ (prefixWord ++ tailWord_530129).sum := by decide
  have hdescent : baseEnd_530129 < baseStart_530129 := by decide
  rcases family_descends (prefixWord ++ tailWord_530129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530149 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_530149 : Nat := 118140960795 + 530149 * 2 ^ 59
def prefixEnd_530149 : Nat := 4983230072969 + 3 ^ 40 * 530149 * 2
def baseEnd_530149 : Nat := 272221255500551523299395

theorem tailTrace_530149 : CollatzResearch.WordTrace tailWord_530149 prefixEnd_530149 272221255500551523299395 := by
  unfold tailWord_530149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19336122556368190085873501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890748370912126723915667 19336122556368190085873501)
  ·
    refine ⟨7251045958638071282202563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19336122556368190085873501 7251045958638071282202563)
    ·
      refine ⟨10876568937957106923303845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7251045958638071282202563 10876568937957106923303845)
      ·
        refine ⟨2039356675866957548119471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10876568937957106923303845 2039356675866957548119471)
        ·
          refine ⟨3059035013800436322179207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039356675866957548119471 3059035013800436322179207)
          ·
            refine ⟨4588552520700654483268811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059035013800436322179207 4588552520700654483268811)
            ·
              refine ⟨6882828781050981724903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588552520700654483268811 6882828781050981724903217)
              ·
                refine ⟨5162121585788236293677413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882828781050981724903217 5162121585788236293677413)
                ·
                  refine ⟨967897797335294305064515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5162121585788236293677413 967897797335294305064515)
                  ·
                    refine ⟨1451846696002941457596773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967897797335294305064515 1451846696002941457596773)
                    ·
                      refine ⟨272221255500551523299395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1451846696002941457596773 272221255500551523299395)
                      ·
                        rfl

theorem cell23_530149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_530149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530149 prefixEnd_530149 := by exact prefixLift 530149
  have htrace : WordTrace (prefixWord ++ tailWord_530149) baseStart_530149 baseEnd_530149 := by
    simpa [prefixWord, tailWord_530149, baseEnd_530149] using wordTrace_append hprefix tailTrace_530149
  have hstable : (prefixWord ++ tailWord_530149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530149).length < 2 ^ (prefixWord ++ tailWord_530149).sum := by decide
  have hdescent : baseEnd_530149 < baseStart_530149 := by decide
  rcases family_descends (prefixWord ++ tailWord_530149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530159 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 5, 4]
def baseStart_530159 : Nat := 118140960795 + 530159 * 2 ^ 59
def prefixEnd_530159 : Nat := 4983230072969 + 3 ^ 40 * 530159 * 2
def baseEnd_530159 : Nat := 90742130102365494724783

theorem tailTrace_530159 : CollatzResearch.WordTrace tailWord_530159 prefixEnd_530159 90742130102365494724783 := by
  unfold tailWord_530159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19336487286331961793737531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12890991524221307862491687 19336487286331961793737531)
  ·
    refine ⟨29004730929497942690606297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19336487286331961793737531 29004730929497942690606297)
    ·
      refine ⟨21753548197123457017954723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29004730929497942690606297 21753548197123457017954723)
      ·
        refine ⟨32630322295685185526932085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21753548197123457017954723 32630322295685185526932085)
        ·
          refine ⟨3059092715220486143149883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32630322295685185526932085 3059092715220486143149883)
          ·
            refine ⟨4588639072830729214724825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059092715220486143149883 4588639072830729214724825)
            ·
              refine ⟨3441479304623046911043619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588639072830729214724825 3441479304623046911043619)
              ·
                refine ⟨5162218956934570366565429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441479304623046911043619 5162218956934570366565429)
                ·
                  refine ⟨483958027212615971865509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5162218956934570366565429 483958027212615971865509)
                  ·
                    refine ⟨90742130102365494724783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 483958027212615971865509 90742130102365494724783)
                    ·
                      rfl

theorem cell23_530159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_530159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530159 prefixEnd_530159 := by exact prefixLift 530159
  have htrace : WordTrace (prefixWord ++ tailWord_530159) baseStart_530159 baseEnd_530159 := by
    simpa [prefixWord, tailWord_530159, baseEnd_530159] using wordTrace_append hprefix tailTrace_530159
  have hstable : (prefixWord ++ tailWord_530159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530159).length < 2 ^ (prefixWord ++ tailWord_530159).sum := by decide
  have hdescent : baseEnd_530159 < baseStart_530159 := by decide
  rcases family_descends (prefixWord ++ tailWord_530159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530166 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_530166 : Nat := 118140960795 + 530166 * 2 ^ 59
def prefixEnd_530166 : Nat := 4983230072969 + 3 ^ 40 * 530166 * 2
def baseEnd_530166 : Nat := 272229984671677956786817

theorem tailTrace_530166 : CollatzResearch.WordTrace tailWord_530166 prefixEnd_530166 272229984671677956786817 := by
  unfold tailWord_530166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208546412331662624327647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12891161731537734659494901 1208546412331662624327647)
  ·
    refine ⟨1812819618497493936491471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208546412331662624327647 1812819618497493936491471)
    ·
      refine ⟨2719229427746240904737207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812819618497493936491471 2719229427746240904737207)
      ·
        refine ⟨4078844141619361357105811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719229427746240904737207 4078844141619361357105811)
        ·
          refine ⟨6118266212429042035658717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078844141619361357105811 6118266212429042035658717)
          ·
            refine ⟨2294349829660890763372019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6118266212429042035658717 2294349829660890763372019)
            ·
              refine ⟨3441524744491336145058029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294349829660890763372019 3441524744491336145058029)
              ·
                refine ⟨1290571779184251054396761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3441524744491336145058029 1290571779184251054396761)
                ·
                  refine ⟨967928834388188290797571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290571779184251054396761 967928834388188290797571)
                  ·
                    refine ⟨1451893251582282436196357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967928834388188290797571 1451893251582282436196357)
                    ·
                      refine ⟨272229984671677956786817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1451893251582282436196357 272229984671677956786817)
                      ·
                        rfl

theorem cell23_530166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_530166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530166 prefixEnd_530166 := by exact prefixLift 530166
  have htrace : WordTrace (prefixWord ++ tailWord_530166) baseStart_530166 baseEnd_530166 := by
    simpa [prefixWord, tailWord_530166, baseEnd_530166] using wordTrace_append hprefix tailTrace_530166
  have hstable : (prefixWord ++ tailWord_530166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530166).length < 2 ^ (prefixWord ++ tailWord_530166).sum := by decide
  have hdescent : baseEnd_530166 < baseStart_530166 := by decide
  rcases family_descends (prefixWord ++ tailWord_530166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530186 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_530186 : Nat := 118140960795 + 530186 * 2 ^ 59
def prefixEnd_530186 : Nat := 4983230072969 + 3 ^ 40 * 530186 * 2
def baseEnd_530186 : Nat := 272240254284767878536725

theorem tailTrace_530186 : CollatzResearch.WordTrace tailWord_530186 prefixEnd_530186 272240254284767878536725 := by
  unfold tailWord_530186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4834368014308536351242603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12891648038156096936646941 4834368014308536351242603)
  ·
    refine ⟨7251552021462804526863905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4834368014308536351242603 7251552021462804526863905)
    ·
      refine ⟨5438664016097103395147929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7251552021462804526863905 5438664016097103395147929)
      ·
        refine ⟨4078998012072827546360947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438664016097103395147929 4078998012072827546360947)
        ·
          refine ⟨6118497018109241319541421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078998012072827546360947 6118497018109241319541421)
          ·
            refine ⟨2294436381790965494828033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6118497018109241319541421 2294436381790965494828033)
            ·
              refine ⟨1720827286343224121121025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2294436381790965494828033 1720827286343224121121025)
              ·
                refine ⟨1290620464757418090840769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720827286343224121121025 1290620464757418090840769)
                ·
                  refine ⟨967965348568063568130577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290620464757418090840769 967965348568063568130577)
                  ·
                    refine ⟨725974011426047676097933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 967965348568063568130577 725974011426047676097933)
                    ·
                      refine ⟨272240254284767878536725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 725974011426047676097933 272240254284767878536725)
                      ·
                        rfl

theorem cell23_530186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_530186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530186 prefixEnd_530186 := by exact prefixLift 530186
  have htrace : WordTrace (prefixWord ++ tailWord_530186) baseStart_530186 baseEnd_530186 := by
    simpa [prefixWord, tailWord_530186, baseEnd_530186] using wordTrace_append hprefix tailTrace_530186
  have hstable : (prefixWord ++ tailWord_530186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530186).length < 2 ^ (prefixWord ++ tailWord_530186).sum := by decide
  have hdescent : baseEnd_530186 < baseStart_530186 := by decide
  rcases family_descends (prefixWord ++ tailWord_530186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530273 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_530273 : Nat := 118140960795 + 530273 * 2 ^ 59
def prefixEnd_530273 : Nat := 4983230072969 + 3 ^ 40 * 530273 * 2
def baseEnd_530273 : Nat := 272284927101709038148825

theorem tailTrace_530273 : CollatzResearch.WordTrace tailWord_530273 prefixEnd_530273 272284927101709038148825 := by
  unfold tailWord_530273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19340645207918959263387473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12893763471945972842258315 19340645207918959263387473)
  ·
    refine ⟨14505483905939219447540605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19340645207918959263387473 14505483905939219447540605)
    ·
      refine ⟨5439556464727207292827727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14505483905939219447540605 5439556464727207292827727)
      ·
        refine ⟨8159334697090810939241591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5439556464727207292827727 8159334697090810939241591)
        ·
          refine ⟨12239002045636216408862387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8159334697090810939241591 12239002045636216408862387)
          ·
            refine ⟨18358503068454324613293581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12239002045636216408862387 18358503068454324613293581)
            ·
              refine ⟨6884438650670371729985093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18358503068454324613293581 6884438650670371729985093)
              ·
                refine ⟨1290832247000694699372205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6884438650670371729985093 1290832247000694699372205)
                ·
                  refine ⟨484062092625260512264577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1290832247000694699372205 484062092625260512264577)
                  ·
                    refine ⟨363046569468945384198433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484062092625260512264577 363046569468945384198433)
                    ·
                      refine ⟨272284927101709038148825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363046569468945384198433 272284927101709038148825)
                      ·
                        rfl

theorem cell23_530273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_530273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530273 prefixEnd_530273 := by exact prefixLift 530273
  have htrace : WordTrace (prefixWord ++ tailWord_530273) baseStart_530273 baseEnd_530273 := by
    simpa [prefixWord, tailWord_530273, baseEnd_530273] using wordTrace_append hprefix tailTrace_530273
  have hstable : (prefixWord ++ tailWord_530273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530273).length < 2 ^ (prefixWord ++ tailWord_530273).sum := by decide
  have hdescent : baseEnd_530273 < baseStart_530273 := by decide
  rcases family_descends (prefixWord ++ tailWord_530273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530279 : List Nat := [1, 1, 5, 1, 2, 1, 3, 9]
def baseStart_530279 : Nat := 118140960795 + 530279 * 2 ^ 59
def prefixEnd_530279 : Nat := 4983230072969 + 3 ^ 40 * 530279 * 2
def baseEnd_530279 : Nat := 10084741036505037580511

theorem tailTrace_530279 : CollatzResearch.WordTrace tailWord_530279 prefixEnd_530279 10084741036505037580511 := by
  unfold tailWord_530279
  simp only [CollatzResearch.WordTrace]
  refine ⟨19340864045897222288105891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12893909363931481525403927 19340864045897222288105891)
  ·
    refine ⟨29011296068845833432158837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19340864045897222288105891 29011296068845833432158837)
    ·
      refine ⟨2719809006454296884264891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29011296068845833432158837 2719809006454296884264891)
      ·
        refine ⟨4079713509681445326397337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719809006454296884264891 4079713509681445326397337)
        ·
          refine ⟨3059785132261083994798003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4079713509681445326397337 3059785132261083994798003)
          ·
            refine ⟨4589677698391625992197005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059785132261083994798003 4589677698391625992197005)
            ·
              refine ⟨1721129136896859747073877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4589677698391625992197005 1721129136896859747073877)
              ·
                refine ⟨10084741036505037580511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1721129136896859747073877 10084741036505037580511)
                ·
                  rfl

theorem cell23_530279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 9].length) (baseStart_530279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530279 prefixEnd_530279 := by exact prefixLift 530279
  have htrace : WordTrace (prefixWord ++ tailWord_530279) baseStart_530279 baseEnd_530279 := by
    simpa [prefixWord, tailWord_530279, baseEnd_530279] using wordTrace_append hprefix tailTrace_530279
  have hstable : (prefixWord ++ tailWord_530279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530279).length < 2 ^ (prefixWord ++ tailWord_530279).sum := by decide
  have hdescent : baseEnd_530279 < baseStart_530279 := by decide
  rcases family_descends (prefixWord ++ tailWord_530279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530293 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_530293 : Nat := 118140960795 + 530293 * 2 ^ 59
def prefixEnd_530293 : Nat := 4983230072969 + 3 ^ 40 * 530293 * 2
def baseEnd_530293 : Nat := 272295196714798959898733

theorem tailTrace_530293 : CollatzResearch.WordTrace tailWord_530293 prefixEnd_530293 272295196714798959898733 := by
  unfold tailWord_530293
  simp only [CollatzResearch.WordTrace]
  refine ⟨19341374667846502679115533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12894249778564335119410355 19341374667846502679115533)
  ·
    refine ⟨7253015500442438504668325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19341374667846502679115533 7253015500442438504668325)
    ·
      refine ⟨1359940406332957219625311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7253015500442438504668325 1359940406332957219625311)
      ·
        refine ⟨2039910609499435829437967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359940406332957219625311 2039910609499435829437967)
        ·
          refine ⟨3059865914249153744156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039910609499435829437967 3059865914249153744156951)
          ·
            refine ⟨4589798871373730616235427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059865914249153744156951 4589798871373730616235427)
            ·
              refine ⟨6884698307060595924353141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589798871373730616235427 6884698307060595924353141)
              ·
                refine ⟨645440466286930867908107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6884698307060595924353141 645440466286930867908107)
                ·
                  refine ⟨968160699430396301862161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645440466286930867908107 968160699430396301862161)
                  ·
                    refine ⟨726120524572797226396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968160699430396301862161 726120524572797226396621)
                    ·
                      refine ⟨272295196714798959898733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726120524572797226396621 272295196714798959898733)
                      ·
                        rfl

theorem cell23_530293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_530293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530293 prefixEnd_530293 := by exact prefixLift 530293
  have htrace : WordTrace (prefixWord ++ tailWord_530293) baseStart_530293 baseEnd_530293 := by
    simpa [prefixWord, tailWord_530293, baseEnd_530293] using wordTrace_append hprefix tailTrace_530293
  have hstable : (prefixWord ++ tailWord_530293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530293).length < 2 ^ (prefixWord ++ tailWord_530293).sum := by decide
  have hdescent : baseEnd_530293 < baseStart_530293 := by decide
  rcases family_descends (prefixWord ++ tailWord_530293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530309 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_530309 : Nat := 118140960795 + 530309 * 2 ^ 59
def prefixEnd_530309 : Nat := 4983230072969 + 3 ^ 40 * 530309 * 2
def baseEnd_530309 : Nat := 90767804135090299099553

theorem tailTrace_530309 : CollatzResearch.WordTrace tailWord_530309 prefixEnd_530309 90767804135090299099553 := by
  unfold tailWord_530309
  simp only [CollatzResearch.WordTrace]
  refine ⟨19341958235788537411697981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12894638823859024941131987 19341958235788537411697981)
  ·
    refine ⟨7253234338420701529386743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19341958235788537411697981 7253234338420701529386743)
    ·
      refine ⟨10879851507631052294080115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7253234338420701529386743 10879851507631052294080115)
      ·
        refine ⟨16319777261446578441120173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10879851507631052294080115 16319777261446578441120173)
        ·
          refine ⟨6119916473042466915420065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16319777261446578441120173 6119916473042466915420065)
          ·
            refine ⟨4589937354781850186565049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6119916473042466915420065 4589937354781850186565049)
            ·
              refine ⟨3442453016086387639923787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589937354781850186565049 3442453016086387639923787)
              ·
                refine ⟨5163679524129581459885681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442453016086387639923787 5163679524129581459885681)
                ·
                  refine ⟨3872759643097186094914261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163679524129581459885681 3872759643097186094914261)
                  ·
                    refine ⟨90767804135090299099553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3872759643097186094914261 90767804135090299099553)
                    ·
                      rfl

theorem cell23_530309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_530309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530309 prefixEnd_530309 := by exact prefixLift 530309
  have htrace : WordTrace (prefixWord ++ tailWord_530309) baseStart_530309 baseEnd_530309 := by
    simpa [prefixWord, tailWord_530309, baseEnd_530309] using wordTrace_append hprefix tailTrace_530309
  have hstable : (prefixWord ++ tailWord_530309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530309).length < 2 ^ (prefixWord ++ tailWord_530309).sum := by decide
  have hdescent : baseEnd_530309 < baseStart_530309 := by decide
  rcases family_descends (prefixWord ++ tailWord_530309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530316 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_530316 : Nat := 118140960795 + 530316 * 2 ^ 59
def prefixEnd_530316 : Nat := 4983230072969 + 3 ^ 40 * 530316 * 2
def baseEnd_530316 : Nat := 272307006769852369911127

theorem tailTrace_530316 : CollatzResearch.WordTrace tailWord_530316 prefixEnd_530316 272307006769852369911127 := by
  unfold tailWord_530316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9671106773381588803601401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12894809031175451738135201 9671106773381588803601401)
  ·
    refine ⟨7253330080036191602701051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9671106773381588803601401 7253330080036191602701051)
    ·
      refine ⟨10879995120054287404051577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7253330080036191602701051 10879995120054287404051577)
      ·
        refine ⟨8159996340040715553038683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10879995120054287404051577 8159996340040715553038683)
        ·
          refine ⟨12239994510061073329558025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8159996340040715553038683 12239994510061073329558025)
          ·
            refine ⟨9179995882545804997168519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12239994510061073329558025 9179995882545804997168519)
            ·
              refine ⟨13769993823818707495752779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9179995882545804997168519 13769993823818707495752779)
              ·
                refine ⟨20654990735728061243629169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13769993823818707495752779 20654990735728061243629169)
                ·
                  refine ⟨15491243051796045932721877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20654990735728061243629169 15491243051796045932721877)
                  ·
                    refine ⟨363076009026469826548169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15491243051796045932721877 363076009026469826548169)
                    ·
                      refine ⟨272307006769852369911127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363076009026469826548169 272307006769852369911127)
                      ·
                        rfl

theorem cell23_530316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_530316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530316 prefixEnd_530316 := by exact prefixLift 530316
  have htrace : WordTrace (prefixWord ++ tailWord_530316) baseStart_530316 baseEnd_530316 := by
    simpa [prefixWord, tailWord_530316, baseEnd_530316] using wordTrace_append hprefix tailTrace_530316
  have hstable : (prefixWord ++ tailWord_530316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530316).length < 2 ^ (prefixWord ++ tailWord_530316).sum := by decide
  have hdescent : baseEnd_530316 < baseStart_530316 := by decide
  rcases family_descends (prefixWord ++ tailWord_530316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530339 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 6]
def baseStart_530339 : Nat := 118140960795 + 530339 * 2 ^ 59
def prefixEnd_530339 : Nat := 4983230072969 + 3 ^ 40 * 530339 * 2
def baseEnd_530339 : Nat := 90772938941635259974507

theorem tailTrace_530339 : CollatzResearch.WordTrace tailWord_530339 prefixEnd_530339 90772938941635259974507 := by
  unfold tailWord_530339
  simp only [CollatzResearch.WordTrace]
  refine ⟨19343052425679852535290071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12895368283786568356860047 19343052425679852535290071)
  ·
    refine ⟨29014578638519778802935107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19343052425679852535290071 29014578638519778802935107)
    ·
      refine ⟨43521867957779668204402661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29014578638519778802935107 43521867957779668204402661)
      ·
        refine ⟨8160350242083687788325499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43521867957779668204402661 8160350242083687788325499)
        ·
          refine ⟨12240525363125531682488249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8160350242083687788325499 12240525363125531682488249)
          ·
            refine ⟨9180394022344148761866187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12240525363125531682488249 9180394022344148761866187)
            ·
              refine ⟨13770591033516223142799281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9180394022344148761866187 13770591033516223142799281)
              ·
                refine ⟨10327943275137167357099461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13770591033516223142799281 10327943275137167357099461)
                ·
                  refine ⟨1936489364088218879456149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10327943275137167357099461 1936489364088218879456149)
                  ·
                    refine ⟨90772938941635259974507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1936489364088218879456149 90772938941635259974507)
                    ·
                      rfl

theorem cell23_530339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_530339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530339 prefixEnd_530339 := by exact prefixLift 530339
  have htrace : WordTrace (prefixWord ++ tailWord_530339) baseStart_530339 baseEnd_530339 := by
    simpa [prefixWord, tailWord_530339, baseEnd_530339] using wordTrace_append hprefix tailTrace_530339
  have hstable : (prefixWord ++ tailWord_530339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530339).length < 2 ^ (prefixWord ++ tailWord_530339).sum := by decide
  have hdescent : baseEnd_530339 < baseStart_530339 := by decide
  rcases family_descends (prefixWord ++ tailWord_530339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530344 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_530344 : Nat := 118140960795 + 530344 * 2 ^ 59
def prefixEnd_530344 : Nat := 4983230072969 + 3 ^ 40 * 530344 * 2
def baseEnd_530344 : Nat := 272321384228178260360999

theorem tailTrace_530344 : CollatzResearch.WordTrace tailWord_530344 prefixEnd_530344 272321384228178260360999 := by
  unfold tailWord_530344
  simp only [CollatzResearch.WordTrace]
  refine ⟨9671617395330869194611043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12895489860441158926148057 9671617395330869194611043)
  ·
    refine ⟨14507426092996303791916565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9671617395330869194611043 14507426092996303791916565)
    ·
      refine ⟨680035598109201740246089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14507426092996303791916565 680035598109201740246089)
      ·
        refine ⟨510026698581901305184567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680035598109201740246089 510026698581901305184567)
        ·
          refine ⟨765040047872851957776851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510026698581901305184567 765040047872851957776851)
          ·
            refine ⟨1147560071809277936665277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765040047872851957776851 1147560071809277936665277)
            ·
              refine ⟨430335026928479226249479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147560071809277936665277 430335026928479226249479)
              ·
                refine ⟨645502540392718839374219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430335026928479226249479 645502540392718839374219)
                ·
                  refine ⟨968253810589078259061329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645502540392718839374219 968253810589078259061329)
                  ·
                    refine ⟨726190357941808694295997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968253810589078259061329 726190357941808694295997)
                    ·
                      refine ⟨272321384228178260360999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726190357941808694295997 272321384228178260360999)
                      ·
                        rfl

theorem cell23_530344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_530344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530344 prefixEnd_530344 := by exact prefixLift 530344
  have htrace : WordTrace (prefixWord ++ tailWord_530344) baseStart_530344 baseEnd_530344 := by
    simpa [prefixWord, tailWord_530344, baseEnd_530344] using wordTrace_append hprefix tailTrace_530344
  have hstable : (prefixWord ++ tailWord_530344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530344).length < 2 ^ (prefixWord ++ tailWord_530344).sum := by decide
  have hdescent : baseEnd_530344 < baseStart_530344 := by decide
  rcases family_descends (prefixWord ++ tailWord_530344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530359 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_530359 : Nat := 118140960795 + 530359 * 2 ^ 59
def prefixEnd_530359 : Nat := 4983230072969 + 3 ^ 40 * 530359 * 2
def baseEnd_530359 : Nat := 272329086437995701673429

theorem tailTrace_530359 : CollatzResearch.WordTrace tailWord_530359 prefixEnd_530359 272329086437995701673429 := by
  unfold tailWord_530359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19343781885607395951018131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12895854590404930634012087 19343781885607395951018131)
  ·
    refine ⟨29015672828411093926527197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19343781885607395951018131 29015672828411093926527197)
    ·
      refine ⟨10880877310654160222447699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29015672828411093926527197 10880877310654160222447699)
      ·
        refine ⟨16321315965981240333671549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880877310654160222447699 16321315965981240333671549)
        ·
          refine ⟨6120493487242965125126831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16321315965981240333671549 6120493487242965125126831)
          ·
            refine ⟨9180740230864447687690247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120493487242965125126831 9180740230864447687690247)
            ·
              refine ⟨13771110346296671531535371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9180740230864447687690247 13771110346296671531535371)
              ·
                refine ⟨20656665519445007297303057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13771110346296671531535371 20656665519445007297303057)
                ·
                  refine ⟨15492499139583755472977293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20656665519445007297303057 15492499139583755472977293)
                  ·
                    refine ⟨5809687177343908302366485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15492499139583755472977293 5809687177343908302366485)
                    ·
                      refine ⟨272329086437995701673429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5809687177343908302366485 272329086437995701673429)
                      ·
                        rfl

theorem cell23_530359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_530359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530359 prefixEnd_530359 := by exact prefixLift 530359
  have htrace : WordTrace (prefixWord ++ tailWord_530359) baseStart_530359 baseEnd_530359 := by
    simpa [prefixWord, tailWord_530359, baseEnd_530359] using wordTrace_append hprefix tailTrace_530359
  have hstable : (prefixWord ++ tailWord_530359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530359).length < 2 ^ (prefixWord ++ tailWord_530359).sum := by decide
  have hdescent : baseEnd_530359 < baseStart_530359 := by decide
  rcases family_descends (prefixWord ++ tailWord_530359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530376 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_530376 : Nat := 118140960795 + 530376 * 2 ^ 59
def prefixEnd_530376 : Nat := 4983230072969 + 3 ^ 40 * 530376 * 2
def baseEnd_530376 : Nat := 272337815609122135160851

theorem tailTrace_530376 : CollatzResearch.WordTrace tailWord_530376 prefixEnd_530376 272337815609122135160851 := by
  unfold tailWord_530376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9672200963272903927193491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12896267951030538569591321 9672200963272903927193491)
  ·
    refine ⟨14508301444909355890790237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9672200963272903927193491 14508301444909355890790237)
    ·
      refine ⟨5440613041841008459046339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14508301444909355890790237 5440613041841008459046339)
      ·
        refine ⟨8160919562761512688569509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440613041841008459046339 8160919562761512688569509)
        ·
          refine ⟨1530172418017783629106783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8160919562761512688569509 1530172418017783629106783)
          ·
            refine ⟨2295258627026675443660175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530172418017783629106783 2295258627026675443660175)
            ·
              refine ⟨3442887940540013165490263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295258627026675443660175 3442887940540013165490263)
              ·
                refine ⟨5164331910810019748235395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442887940540013165490263 5164331910810019748235395)
                ·
                  refine ⟨7746497866215029622353093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164331910810019748235395 7746497866215029622353093)
                  ·
                    refine ⟨1452468349915318054191205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7746497866215029622353093 1452468349915318054191205)
                    ·
                      refine ⟨272337815609122135160851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1452468349915318054191205 272337815609122135160851)
                      ·
                        rfl

theorem cell23_530376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_530376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530376 prefixEnd_530376 := by exact prefixLift 530376
  have htrace : WordTrace (prefixWord ++ tailWord_530376) baseStart_530376 baseEnd_530376 := by
    simpa [prefixWord, tailWord_530376, baseEnd_530376] using wordTrace_append hprefix tailTrace_530376
  have hstable : (prefixWord ++ tailWord_530376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530376).length < 2 ^ (prefixWord ++ tailWord_530376).sum := by decide
  have hdescent : baseEnd_530376 < baseStart_530376 := by decide
  rcases family_descends (prefixWord ++ tailWord_530376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530380 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_530380 : Nat := 118140960795 + 530380 * 2 ^ 59
def prefixEnd_530380 : Nat := 4983230072969 + 3 ^ 40 * 530380 * 2
def baseEnd_530380 : Nat := 272339869531740119510833

theorem tailTrace_530380 : CollatzResearch.WordTrace tailWord_530380 prefixEnd_530380 272339869531740119510833 := by
  unfold tailWord_530380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9672273909265658268766297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12896365212354211025021729 9672273909265658268766297)
  ·
    refine ⟨7254205431949243701574723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9672273909265658268766297 7254205431949243701574723)
    ·
      refine ⟨10881308147923865552362085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7254205431949243701574723 10881308147923865552362085)
      ·
        refine ⟨2040245277735724791067891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10881308147923865552362085 2040245277735724791067891)
        ·
          refine ⟨3060367916603587186601837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040245277735724791067891 3060367916603587186601837)
          ·
            refine ⟨1147637968726345194975689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3060367916603587186601837 1147637968726345194975689)
            ·
              refine ⟨860728476544758896231767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147637968726345194975689 860728476544758896231767)
              ·
                refine ⟨1291092714817138344347651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860728476544758896231767 1291092714817138344347651)
                ·
                  refine ⟨1936639072225707516521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291092714817138344347651 1936639072225707516521477)
                  ·
                    refine ⟨363119826042320159347777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1936639072225707516521477 363119826042320159347777)
                    ·
                      refine ⟨272339869531740119510833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363119826042320159347777 272339869531740119510833)
                      ·
                        rfl

theorem cell23_530380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_530380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530380 prefixEnd_530380 := by exact prefixLift 530380
  have htrace : WordTrace (prefixWord ++ tailWord_530380) baseStart_530380 baseEnd_530380 := by
    simpa [prefixWord, tailWord_530380, baseEnd_530380] using wordTrace_append hprefix tailTrace_530380
  have hstable : (prefixWord ++ tailWord_530380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530380).length < 2 ^ (prefixWord ++ tailWord_530380).sum := by decide
  have hdescent : baseEnd_530380 < baseStart_530380 := by decide
  rcases family_descends (prefixWord ++ tailWord_530380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530403 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 5]
def baseStart_530403 : Nat := 118140960795 + 530403 * 2 ^ 59
def prefixEnd_530403 : Nat := 4983230072969 + 3 ^ 40 * 530403 * 2
def baseEnd_530403 : Nat := 30261297731865947724803

theorem tailTrace_530403 : CollatzResearch.WordTrace tailWord_530403 prefixEnd_530403 30261297731865947724803 := by
  unfold tailWord_530403
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345386697447991465619863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12896924464965327643746575 19345386697447991465619863)
  ·
    refine ⟨29018080046171987198429795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19345386697447991465619863 29018080046171987198429795)
    ·
      refine ⟨43527120069257980797644693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29018080046171987198429795 43527120069257980797644693)
      ·
        refine ⟨2040333753246467849889595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43527120069257980797644693 2040333753246467849889595)
        ·
          refine ⟨3060500629869701774834393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040333753246467849889595 3060500629869701774834393)
          ·
            refine ⟨2295375472402276331125795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060500629869701774834393 2295375472402276331125795)
            ·
              refine ⟨3443063208603414496688693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295375472402276331125795 3443063208603414496688693)
              ·
                refine ⟨322787175806570109064565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3443063208603414496688693 322787175806570109064565)
                ·
                  refine ⟨30261297731865947724803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322787175806570109064565 30261297731865947724803)
                  ·
                    rfl

theorem cell23_530403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 5].length) (baseStart_530403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530403 prefixEnd_530403 := by exact prefixLift 530403
  have htrace : WordTrace (prefixWord ++ tailWord_530403) baseStart_530403 baseEnd_530403 := by
    simpa [prefixWord, tailWord_530403, baseEnd_530403] using wordTrace_append hprefix tailTrace_530403
  have hstable : (prefixWord ++ tailWord_530403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530403).length < 2 ^ (prefixWord ++ tailWord_530403).sum := by decide
  have hdescent : baseEnd_530403 < baseStart_530403 := by decide
  rcases family_descends (prefixWord ++ tailWord_530403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530414 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_530414 : Nat := 118140960795 + 530414 * 2 ^ 59
def prefixEnd_530414 : Nat := 4983230072969 + 3 ^ 40 * 530414 * 2
def baseEnd_530414 : Nat := 272357327873992986485677

theorem tailTrace_530414 : CollatzResearch.WordTrace tailWord_530414 prefixEnd_530414 272357327873992986485677 := by
  unfold tailWord_530414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418223487551017543033787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12897191933605426896180197 2418223487551017543033787)
  ·
    refine ⟨3627335231326526314550681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418223487551017543033787 3627335231326526314550681)
    ·
      refine ⟨2720501423494894735913011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3627335231326526314550681 2720501423494894735913011)
      ·
        refine ⟨4080752135242342103869517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720501423494894735913011 4080752135242342103869517)
        ·
          refine ⟨1530282050715878288951069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4080752135242342103869517 1530282050715878288951069)
          ·
            refine ⟨573855769018454358356651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1530282050715878288951069 573855769018454358356651)
            ·
              refine ⟨860783653527681537534977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573855769018454358356651 860783653527681537534977)
              ·
                refine ⟨645587740145761153151233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860783653527681537534977 645587740145761153151233)
                ·
                  refine ⟨484190805109320864863425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645587740145761153151233 484190805109320864863425)
                  ·
                    refine ⟨363143103831990648647569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484190805109320864863425 363143103831990648647569)
                    ·
                      refine ⟨272357327873992986485677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363143103831990648647569 272357327873992986485677)
                      ·
                        rfl

theorem cell23_530414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_530414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530414 prefixEnd_530414 := by exact prefixLift 530414
  have htrace : WordTrace (prefixWord ++ tailWord_530414) baseStart_530414 baseEnd_530414 := by
    simpa [prefixWord, tailWord_530414, baseEnd_530414] using wordTrace_append hprefix tailTrace_530414
  have hstable : (prefixWord ++ tailWord_530414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530414).length < 2 ^ (prefixWord ++ tailWord_530414).sum := by decide
  have hdescent : baseEnd_530414 < baseStart_530414 := by decide
  rcases family_descends (prefixWord ++ tailWord_530414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530416 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_530416 : Nat := 118140960795 + 530416 * 2 ^ 59
def prefixEnd_530416 : Nat := 4983230072969 + 3 ^ 40 * 530416 * 2
def baseEnd_530416 : Nat := 90786118278433992886889

theorem tailTrace_530416 : CollatzResearch.WordTrace tailWord_530416 prefixEnd_530416 90786118278433992886889 := by
  unfold tailWord_530416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9672930423200447342921551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12897240564267263123895401 9672930423200447342921551)
  ·
    refine ⟨14509395634800671014382327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9672930423200447342921551 14509395634800671014382327)
    ·
      refine ⟨21764093452201006521573491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14509395634800671014382327 21764093452201006521573491)
      ·
        refine ⟨32646140178301509782360237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21764093452201006521573491 32646140178301509782360237)
        ·
          refine ⟨12242302566863066168385089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32646140178301509782360237 12242302566863066168385089)
          ·
            refine ⟨9181726925147299626288817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12242302566863066168385089 9181726925147299626288817)
            ·
              refine ⟨6886295193860474719716613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9181726925147299626288817 6886295193860474719716613)
              ·
                refine ⟨1291180348848839009946865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6886295193860474719716613 1291180348848839009946865)
                ·
                  refine ⟨968385261636629257460149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291180348848839009946865 968385261636629257460149)
                  ·
                    refine ⟨90786118278433992886889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 968385261636629257460149 90786118278433992886889)
                    ·
                      rfl

theorem cell23_530416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_530416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530416 prefixEnd_530416 := by exact prefixLift 530416
  have htrace : WordTrace (prefixWord ++ tailWord_530416) baseStart_530416 baseEnd_530416 := by
    simpa [prefixWord, tailWord_530416, baseEnd_530416] using wordTrace_append hprefix tailTrace_530416
  have hstable : (prefixWord ++ tailWord_530416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530416).length < 2 ^ (prefixWord ++ tailWord_530416).sum := by decide
  have hdescent : baseEnd_530416 < baseStart_530416 := by decide
  rcases family_descends (prefixWord ++ tailWord_530416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530430 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_530430 : Nat := 118140960795 + 530430 * 2 ^ 59
def prefixEnd_530430 : Nat := 4983230072969 + 3 ^ 40 * 530430 * 2
def baseEnd_530430 : Nat := 272365543564464923885603

theorem tailTrace_530430 : CollatzResearch.WordTrace tailWord_530430 prefixEnd_530430 272365543564464923885603 := by
  unfold tailWord_530430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418296433543771884606593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12897580978900116717901829 2418296433543771884606593)
  ·
    refine ⟨1813722325157828913454945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2418296433543771884606593 1813722325157828913454945)
    ·
      refine ⟨1360291743868371685091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813722325157828913454945 1360291743868371685091209)
      ·
        refine ⟨1020218807901278763818407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360291743868371685091209 1020218807901278763818407)
        ·
          refine ⟨1530328211851918145727611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020218807901278763818407 1530328211851918145727611)
          ·
            refine ⟨2295492317777877218591417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530328211851918145727611 2295492317777877218591417)
            ·
              refine ⟨1721619238333407913943563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2295492317777877218591417 1721619238333407913943563)
              ·
                refine ⟨2582428857500111870915345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721619238333407913943563 2582428857500111870915345)
                ·
                  refine ⟨1936821643125083903186509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582428857500111870915345 1936821643125083903186509)
                  ·
                    refine ⟨726308116171906463694941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936821643125083903186509 726308116171906463694941)
                    ·
                      refine ⟨272365543564464923885603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726308116171906463694941 272365543564464923885603)
                      ·
                        rfl

theorem cell23_530430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_530430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530430 prefixEnd_530430 := by exact prefixLift 530430
  have htrace : WordTrace (prefixWord ++ tailWord_530430) baseStart_530430 baseEnd_530430 := by
    simpa [prefixWord, tailWord_530430, baseEnd_530430] using wordTrace_append hprefix tailTrace_530430
  have hstable : (prefixWord ++ tailWord_530430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530430).length < 2 ^ (prefixWord ++ tailWord_530430).sum := by decide
  have hdescent : baseEnd_530430 < baseStart_530430 := by decide
  rcases family_descends (prefixWord ++ tailWord_530430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530446 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_530446 : Nat := 118140960795 + 530446 * 2 ^ 59
def prefixEnd_530446 : Nat := 4983230072969 + 3 ^ 40 * 530446 * 2
def baseEnd_530446 : Nat := 90791253084978953761843

theorem tailTrace_530446 : CollatzResearch.WordTrace tailWord_530446 prefixEnd_530446 90791253084978953761843 := by
  unfold tailWord_530446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418369379536526226179399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12897970024194806539623461 2418369379536526226179399)
  ·
    refine ⟨3627554069304789339269099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418369379536526226179399 3627554069304789339269099)
    ·
      refine ⟨5441331103957184008903649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627554069304789339269099 5441331103957184008903649)
      ·
        refine ⟨4080998327967888006677737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5441331103957184008903649 4080998327967888006677737)
        ·
          refine ⟨3060748745975916005008303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080998327967888006677737 3060748745975916005008303)
          ·
            refine ⟨4591123118963874007512455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060748745975916005008303 4591123118963874007512455)
            ·
              refine ⟨6886684678445811011268683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591123118963874007512455 6886684678445811011268683)
              ·
                refine ⟨10330027017668716516903025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6886684678445811011268683 10330027017668716516903025)
                ·
                  refine ⟨7747520263251537387677269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10330027017668716516903025 7747520263251537387677269)
                  ·
                    refine ⟨90791253084978953761843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7747520263251537387677269 90791253084978953761843)
                    ·
                      rfl

theorem cell23_530446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_530446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530446 prefixEnd_530446 := by exact prefixLift 530446
  have htrace : WordTrace (prefixWord ++ tailWord_530446) baseStart_530446 baseEnd_530446 := by
    simpa [prefixWord, tailWord_530446, baseEnd_530446] using wordTrace_append hprefix tailTrace_530446
  have hstable : (prefixWord ++ tailWord_530446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530446).length < 2 ^ (prefixWord ++ tailWord_530446).sum := by decide
  have hdescent : baseEnd_530446 < baseStart_530446 := by decide
  rcases family_descends (prefixWord ++ tailWord_530446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530480 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_530480 : Nat := 118140960795 + 530480 * 2 ^ 59
def prefixEnd_530480 : Nat := 4983230072969 + 3 ^ 40 * 530480 * 2
def baseEnd_530480 : Nat := 90797072532396576086791

theorem tailTrace_530480 : CollatzResearch.WordTrace tailWord_530480 prefixEnd_530480 90797072532396576086791 := by
  unfold tailWord_530480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674097559084516808086447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12898796745446022410781929 9674097559084516808086447)
  ·
    refine ⟨14511146338626775212129671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674097559084516808086447 14511146338626775212129671)
    ·
      refine ⟨21766719507940162818194507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14511146338626775212129671 21766719507940162818194507)
      ·
        refine ⟨32650079261910244227291761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21766719507940162818194507 32650079261910244227291761)
        ·
          refine ⟨24487559446432683170468821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32650079261910244227291761 24487559446432683170468821)
          ·
            refine ⟨573927174525766011807863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24487559446432683170468821 573927174525766011807863)
            ·
              refine ⟨860890761788649017711795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573927174525766011807863 860890761788649017711795)
              ·
                refine ⟨1291336142682973526567693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860890761788649017711795 1291336142682973526567693)
                ·
                  refine ⟨484251053506115072462885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1291336142682973526567693 484251053506115072462885)
                  ·
                    refine ⟨90797072532396576086791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484251053506115072462885 90797072532396576086791)
                    ·
                      rfl

theorem cell23_530480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_530480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530480 prefixEnd_530480 := by exact prefixLift 530480
  have htrace : WordTrace (prefixWord ++ tailWord_530480) baseStart_530480 baseEnd_530480 := by
    simpa [prefixWord, tailWord_530480, baseEnd_530480] using wordTrace_append hprefix tailTrace_530480
  have hstable : (prefixWord ++ tailWord_530480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530480).length < 2 ^ (prefixWord ++ tailWord_530480).sum := by decide
  have hdescent : baseEnd_530480 < baseStart_530480 := by decide
  rcases family_descends (prefixWord ++ tailWord_530480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530493 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 6]
def baseStart_530493 : Nat := 118140960795 + 530493 * 2 ^ 59
def prefixEnd_530493 : Nat := 4983230072969 + 3 ^ 40 * 530493 * 2
def baseEnd_530493 : Nat := 30266432538410908599757

theorem tailTrace_530493 : CollatzResearch.WordTrace tailWord_530493 prefixEnd_530493 30266432538410908599757 := by
  unfold tailWord_530493
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348669267121936836396133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12899112844747957890930755 19348669267121936836396133)
  ·
    refine ⟨3627875487585363156824275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19348669267121936836396133 3627875487585363156824275)
    ·
      refine ⟨5441813231378044735236413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627875487585363156824275 5441813231378044735236413)
      ·
        refine ⟨2040679961766766775713655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5441813231378044735236413 2040679961766766775713655)
        ·
          refine ⟨3061019942650150163570483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040679961766766775713655 3061019942650150163570483)
          ·
            refine ⟨4591529913975225245355725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061019942650150163570483 4591529913975225245355725)
            ·
              refine ⟨1721823717740709467008397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4591529913975225245355725 1721823717740709467008397)
              ·
                refine ⟨645683894152766050128149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1721823717740709467008397 645683894152766050128149)
                ·
                  refine ⟨30266432538410908599757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 645683894152766050128149 30266432538410908599757)
                  ·
                    rfl

theorem cell23_530493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_530493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530493 prefixEnd_530493 := by exact prefixLift 530493
  have htrace : WordTrace (prefixWord ++ tailWord_530493) baseStart_530493 baseEnd_530493 := by
    simpa [prefixWord, tailWord_530493, baseEnd_530493] using wordTrace_append hprefix tailTrace_530493
  have hstable : (prefixWord ++ tailWord_530493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530493).length < 2 ^ (prefixWord ++ tailWord_530493).sum := by decide
  have hdescent : baseEnd_530493 < baseStart_530493 := by decide
  rcases family_descends (prefixWord ++ tailWord_530493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530537 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 1, 1, 3]
def baseStart_530537 : Nat := 118140960795 + 530537 * 2 ^ 59
def prefixEnd_530537 : Nat := 4983230072969 + 3 ^ 40 * 530537 * 2
def baseEnd_530537 : Nat := 272420485994496005247611

theorem tailTrace_530537 : CollatzResearch.WordTrace tailWord_530537 prefixEnd_530537 272420485994496005247611 := by
  unfold tailWord_530537
  simp only [CollatzResearch.WordTrace]
  refine ⟨19350274078962532350997865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12900182719308354900665243 19350274078962532350997865)
  ·
    refine ⟨14512705559221899263248399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19350274078962532350997865 14512705559221899263248399)
    ·
      refine ⟨21769058338832848894872599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512705559221899263248399 21769058338832848894872599)
      ·
        refine ⟨32653587508249273342308899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21769058338832848894872599 32653587508249273342308899)
        ·
          refine ⟨48980381262373910013463349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32653587508249273342308899 48980381262373910013463349)
          ·
            refine ⟨4591910743347554063762189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48980381262373910013463349 4591910743347554063762189)
            ·
              refine ⟨1721966528755332773910821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4591910743347554063762189 1721966528755332773910821)
              ·
                refine ⟨322868724141624895108279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1721966528755332773910821 322868724141624895108279)
                ·
                  refine ⟨484303086212437342662419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322868724141624895108279 484303086212437342662419)
                  ·
                    refine ⟨726454629318656013993629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484303086212437342662419 726454629318656013993629)
                    ·
                      refine ⟨272420485994496005247611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726454629318656013993629 272420485994496005247611)
                      ·
                        rfl

theorem cell23_530537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 1, 3].length) (baseStart_530537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530537 prefixEnd_530537 := by exact prefixLift 530537
  have htrace : WordTrace (prefixWord ++ tailWord_530537) baseStart_530537 baseEnd_530537 := by
    simpa [prefixWord, tailWord_530537, baseEnd_530537] using wordTrace_append hprefix tailTrace_530537
  have hstable : (prefixWord ++ tailWord_530537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530537).length < 2 ^ (prefixWord ++ tailWord_530537).sum := by decide
  have hdescent : baseEnd_530537 < baseStart_530537 := by decide
  rcases family_descends (prefixWord ++ tailWord_530537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530543 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_530543 : Nat := 118140960795 + 530543 * 2 ^ 59
def prefixEnd_530543 : Nat := 4983230072969 + 3 ^ 40 * 530543 * 2
def baseEnd_530543 : Nat := 272423566878422981772583

theorem tailTrace_530543 : CollatzResearch.WordTrace tailWord_530543 prefixEnd_530543 272423566878422981772583 := by
  unfold tailWord_530543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19350492916940795375716283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12900328611293863583810855 19350492916940795375716283)
  ·
    refine ⟨29025739375411193063574425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19350492916940795375716283 29025739375411193063574425)
    ·
      refine ⟨21769304531558394797680819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29025739375411193063574425 21769304531558394797680819)
      ·
        refine ⟨32653956797337592196521229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21769304531558394797680819 32653956797337592196521229)
        ·
          refine ⟨12245233799001597073695461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32653956797337592196521229 12245233799001597073695461)
          ·
            refine ⟨2295981337312799451317899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12245233799001597073695461 2295981337312799451317899)
            ·
              refine ⟨3443972005969199176976849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295981337312799451317899 3443972005969199176976849)
              ·
                refine ⟨2582979004476899382732637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443972005969199176976849 2582979004476899382732637)
                ·
                  refine ⟨968617126678837268524739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2582979004476899382732637 968617126678837268524739)
                  ·
                    refine ⟨1452925690018255902787109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968617126678837268524739 1452925690018255902787109)
                    ·
                      refine ⟨272423566878422981772583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1452925690018255902787109 272423566878422981772583)
                      ·
                        rfl

theorem cell23_530543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_530543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530543 prefixEnd_530543 := by exact prefixLift 530543
  have htrace : WordTrace (prefixWord ++ tailWord_530543) baseStart_530543 baseEnd_530543 := by
    simpa [prefixWord, tailWord_530543, baseEnd_530543] using wordTrace_append hprefix tailTrace_530543
  have hstable : (prefixWord ++ tailWord_530543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530543).length < 2 ^ (prefixWord ++ tailWord_530543).sum := by decide
  have hdescent : baseEnd_530543 < baseStart_530543 := by decide
  rcases family_descends (prefixWord ++ tailWord_530543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530553 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_530553 : Nat := 118140960795 + 530553 * 2 ^ 59
def prefixEnd_530553 : Nat := 4983230072969 + 3 ^ 40 * 530553 * 2
def baseEnd_530553 : Nat := 90809567228322647549179

theorem tailTrace_530553 : CollatzResearch.WordTrace tailWord_530553 prefixEnd_530553 90809567228322647549179 := by
  unfold tailWord_530553
  simp only [CollatzResearch.WordTrace]
  refine ⟨19350857646904567083580313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12900571764603044722386875 19350857646904567083580313)
  ·
    refine ⟨14513143235178425312685235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19350857646904567083580313 14513143235178425312685235)
    ·
      refine ⟨21769714852767637969027853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14513143235178425312685235 21769714852767637969027853)
      ·
        refine ⟨8163643069787864238385445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21769714852767637969027853 8163643069787864238385445)
        ·
          refine ⟨1530683075585224544697271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8163643069787864238385445 1530683075585224544697271)
          ·
            refine ⟨2296024613377836817045907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530683075585224544697271 2296024613377836817045907)
            ·
              refine ⟨3444036920066755225568861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296024613377836817045907 3444036920066755225568861)
              ·
                refine ⟨1291513845025033209588323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3444036920066755225568861 1291513845025033209588323)
                ·
                  refine ⟨1937270767537549814382485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291513845025033209588323 1937270767537549814382485)
                  ·
                    refine ⟨90809567228322647549179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1937270767537549814382485 90809567228322647549179)
                    ·
                      rfl

theorem cell23_530553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_530553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530553 prefixEnd_530553 := by exact prefixLift 530553
  have htrace : WordTrace (prefixWord ++ tailWord_530553) baseStart_530553 baseEnd_530553 := by
    simpa [prefixWord, tailWord_530553, baseEnd_530553] using wordTrace_append hprefix tailTrace_530553
  have hstable : (prefixWord ++ tailWord_530553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530553).length < 2 ^ (prefixWord ++ tailWord_530553).sum := by decide
  have hdescent : baseEnd_530553 < baseStart_530553 := by decide
  rcases family_descends (prefixWord ++ tailWord_530553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530574 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_530574 : Nat := 118140960795 + 530574 * 2 ^ 59
def prefixEnd_530574 : Nat := 4983230072969 + 3 ^ 40 * 530574 * 2
def baseEnd_530574 : Nat := 90813161592904120161647

theorem tailTrace_530574 : CollatzResearch.WordTrace tailWord_530574 prefixEnd_530574 90813161592904120161647 := by
  unfold tailWord_530574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418952947478560958761847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12901082386552325113396517 2418952947478560958761847)
  ·
    refine ⟨3628429421217841438142771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418952947478560958761847 3628429421217841438142771)
    ·
      refine ⟨5442644131826762157214157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628429421217841438142771 5442644131826762157214157)
      ·
        refine ⟨2040991549435035808955309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5442644131826762157214157 2040991549435035808955309)
        ·
          refine ⟨765371831038138428358241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2040991549435035808955309 765371831038138428358241)
          ·
            refine ⟨574028873278603821268681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765371831038138428358241 574028873278603821268681)
            ·
              refine ⟨430521654958952865951511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574028873278603821268681 430521654958952865951511)
              ·
                refine ⟨645782482438429298927267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430521654958952865951511 645782482438429298927267)
                ·
                  refine ⟨968673723657643948390901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645782482438429298927267 968673723657643948390901)
                  ·
                    refine ⟨90813161592904120161647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 968673723657643948390901 90813161592904120161647)
                    ·
                      rfl

theorem cell23_530574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_530574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530574 prefixEnd_530574 := by exact prefixLift 530574
  have htrace : WordTrace (prefixWord ++ tailWord_530574) baseStart_530574 baseEnd_530574 := by
    simpa [prefixWord, tailWord_530574, baseEnd_530574] using wordTrace_append hprefix tailTrace_530574
  have hstable : (prefixWord ++ tailWord_530574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530574).length < 2 ^ (prefixWord ++ tailWord_530574).sum := by decide
  have hdescent : baseEnd_530574 < baseStart_530574 := by decide
  rcases family_descends (prefixWord ++ tailWord_530574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530583 : List Nat := [1, 1, 3, 3, 4, 1, 10]
def baseStart_530583 : Nat := 118140960795 + 530583 * 2 ^ 59
def prefixEnd_530583 : Nat := 4983230072969 + 3 ^ 40 * 530583 * 2
def baseEnd_530583 : Nat := 3363507482772874386079

theorem tailTrace_530583 : CollatzResearch.WordTrace tailWord_530583 prefixEnd_530583 3363507482772874386079 := by
  unfold tailWord_530583
  simp only [CollatzResearch.WordTrace]
  refine ⟨19351951836795882207172403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12901301224530588138114935 19351951836795882207172403)
  ·
    refine ⟨29027927755193823310758605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19351951836795882207172403 29027927755193823310758605)
    ·
      refine ⟨10885472908197683741534477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29027927755193823310758605 10885472908197683741534477)
      ·
        refine ⟨4082052340574131403075429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10885472908197683741534477 4082052340574131403075429)
        ·
          refine ⟨765384813857649638076643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4082052340574131403075429 765384813857649638076643)
          ·
            refine ⟨1148077220786474457114965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765384813857649638076643 1148077220786474457114965)
            ·
              refine ⟨3363507482772874386079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1148077220786474457114965 3363507482772874386079)
              ·
                rfl

theorem cell23_530583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 10].length) (baseStart_530583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530583 prefixEnd_530583 := by exact prefixLift 530583
  have htrace : WordTrace (prefixWord ++ tailWord_530583) baseStart_530583 baseEnd_530583 := by
    simpa [prefixWord, tailWord_530583, baseEnd_530583] using wordTrace_append hprefix tailTrace_530583
  have hstable : (prefixWord ++ tailWord_530583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530583).length < 2 ^ (prefixWord ++ tailWord_530583).sum := by decide
  have hdescent : baseEnd_530583 < baseStart_530583 := by decide
  rcases family_descends (prefixWord ++ tailWord_530583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530594 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_530594 : Nat := 118140960795 + 530594 * 2 ^ 59
def prefixEnd_530594 : Nat := 4983230072969 + 3 ^ 40 * 530594 * 2
def baseEnd_530594 : Nat := 272449754391802282234849

theorem tailTrace_530594 : CollatzResearch.WordTrace tailWord_530594 prefixEnd_530594 272449754391802282234849 := by
  unfold tailWord_530594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838088259939007771455709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12901568693170687390548557 4838088259939007771455709)
  ·
    refine ⟨1814283097477127914295891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4838088259939007771455709 1814283097477127914295891)
    ·
      refine ⟨2721424646215691871443837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814283097477127914295891 2721424646215691871443837)
      ·
        refine ⟨1020534242330884451791439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2721424646215691871443837 1020534242330884451791439)
        ·
          refine ⟨1530801363496326677687159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020534242330884451791439 1530801363496326677687159)
          ·
            refine ⟨2296202045244490016530739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530801363496326677687159 2296202045244490016530739)
            ·
              refine ⟨3444303067866735024796109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296202045244490016530739 3444303067866735024796109)
              ·
                refine ⟨1291613650450025634298541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3444303067866735024796109 1291613650450025634298541)
                ·
                  refine ⟨484355118918759612861953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1291613650450025634298541 484355118918759612861953)
                  ·
                    refine ⟨363266339189069709646465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484355118918759612861953 363266339189069709646465)
                    ·
                      refine ⟨272449754391802282234849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363266339189069709646465 272449754391802282234849)
                      ·
                        rfl

theorem cell23_530594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_530594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530594 prefixEnd_530594 := by exact prefixLift 530594
  have htrace : WordTrace (prefixWord ++ tailWord_530594) baseStart_530594 baseEnd_530594 := by
    simpa [prefixWord, tailWord_530594, baseEnd_530594] using wordTrace_append hprefix tailTrace_530594
  have hstable : (prefixWord ++ tailWord_530594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530594).length < 2 ^ (prefixWord ++ tailWord_530594).sum := by decide
  have hdescent : baseEnd_530594 < baseStart_530594 := by decide
  rcases family_descends (prefixWord ++ tailWord_530594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530628 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_530628 : Nat := 118140960795 + 530628 * 2 ^ 59
def prefixEnd_530628 : Nat := 4983230072969 + 3 ^ 40 * 530628 * 2
def baseEnd_530628 : Nat := 272467212734055149209693

theorem tailTrace_530628 : CollatzResearch.WordTrace tailWord_530628 prefixEnd_530628 272467212734055149209693 := by
  unfold tailWord_530628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676796560816427446280269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12902395414421903261707025 9676796560816427446280269)
  ·
    refine ⟨3628798710306160292355101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9676796560816427446280269 3628798710306160292355101)
    ·
      refine ⟨1360799516364810109633163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3628798710306160292355101 1360799516364810109633163)
      ·
        refine ⟨2041199274547215164449745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360799516364810109633163 2041199274547215164449745)
        ·
          refine ⟨1530899455910411373337309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041199274547215164449745 1530899455910411373337309)
          ·
            refine ⟨574087295966404265001491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1530899455910411373337309 574087295966404265001491)
            ·
              refine ⟨861130943949606397502237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574087295966404265001491 861130943949606397502237)
              ·
                refine ⟨322924103981102399063339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861130943949606397502237 322924103981102399063339)
                ·
                  refine ⟨484386155971653598595009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322924103981102399063339 484386155971653598595009)
                  ·
                    refine ⟨363289616978740198946257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484386155971653598595009 363289616978740198946257)
                    ·
                      refine ⟨272467212734055149209693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363289616978740198946257 272467212734055149209693)
                      ·
                        rfl

theorem cell23_530628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_530628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530628 prefixEnd_530628 := by exact prefixLift 530628
  have htrace : WordTrace (prefixWord ++ tailWord_530628) baseStart_530628 baseEnd_530628 := by
    simpa [prefixWord, tailWord_530628, baseEnd_530628] using wordTrace_append hprefix tailTrace_530628
  have hstable : (prefixWord ++ tailWord_530628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530628).length < 2 ^ (prefixWord ++ tailWord_530628).sum := by decide
  have hdescent : baseEnd_530628 < baseStart_530628 := by decide
  rcases family_descends (prefixWord ++ tailWord_530628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530661 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 2, 1, 3]
def baseStart_530661 : Nat := 118140960795 + 530661 * 2 ^ 59
def prefixEnd_530661 : Nat := 4983230072969 + 3 ^ 40 * 530661 * 2
def baseEnd_530661 : Nat := 272484157595653520097041

theorem tailTrace_530661 : CollatzResearch.WordTrace tailWord_530661 prefixEnd_530661 272484157595653520097041 := by
  unfold tailWord_530661
  simp only [CollatzResearch.WordTrace]
  refine ⟨19354796730513301528511837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12903197820342201019007891 19354796730513301528511837)
  ·
    refine ⟨7258048773942488073191939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19354796730513301528511837 7258048773942488073191939)
    ·
      refine ⟨10887073160913732109787909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7258048773942488073191939 10887073160913732109787909)
      ·
        refine ⟨2041326217671324770585233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10887073160913732109787909 2041326217671324770585233)
        ·
          refine ⟨1530994663253493577938925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2041326217671324770585233 1530994663253493577938925)
          ·
            refine ⟨574122998720060091727097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1530994663253493577938925 574122998720060091727097)
            ·
              refine ⟨430592249040045068795323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574122998720060091727097 430592249040045068795323)
              ·
                refine ⟨645888373560067603192985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430592249040045068795323 645888373560067603192985)
                ·
                  refine ⟨484416280170050702394739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645888373560067603192985 484416280170050702394739)
                  ·
                    refine ⟨726624420255076053592109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484416280170050702394739 726624420255076053592109)
                    ·
                      refine ⟨272484157595653520097041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726624420255076053592109 272484157595653520097041)
                      ·
                        rfl

theorem cell23_530661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_530661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530661 prefixEnd_530661 := by exact prefixLift 530661
  have htrace : WordTrace (prefixWord ++ tailWord_530661) baseStart_530661 baseEnd_530661 := by
    simpa [prefixWord, tailWord_530661, baseEnd_530661] using wordTrace_append hprefix tailTrace_530661
  have hstable : (prefixWord ++ tailWord_530661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530661).length < 2 ^ (prefixWord ++ tailWord_530661).sum := by decide
  have hdescent : baseEnd_530661 < baseStart_530661 := by decide
  rcases family_descends (prefixWord ++ tailWord_530661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530673 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 7]
def baseStart_530673 : Nat := 118140960795 + 530673 * 2 ^ 59
def prefixEnd_530673 : Nat := 4983230072969 + 3 ^ 40 * 530673 * 2
def baseEnd_530673 : Nat := 30276702151500830349665

theorem tailTrace_530673 : CollatzResearch.WordTrace tailWord_530673 prefixEnd_530673 30276702151500830349665 := by
  unfold tailWord_530673
  simp only [CollatzResearch.WordTrace]
  refine ⟨19355234406469827577948673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12903489604313218385299115 19355234406469827577948673)
  ·
    refine ⟨14516425804852370683461505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19355234406469827577948673 14516425804852370683461505)
    ·
      refine ⟨10887319353639278012596129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14516425804852370683461505 10887319353639278012596129)
      ·
        refine ⟨8165489515229458509447097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10887319353639278012596129 8165489515229458509447097)
        ·
          refine ⟨6124117136422093882085323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8165489515229458509447097 6124117136422093882085323)
          ·
            refine ⟨9186175704633140823127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6124117136422093882085323 9186175704633140823127985)
            ·
              refine ⟨6889631778474855617345989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9186175704633140823127985 6889631778474855617345989)
              ·
                refine ⟨1291805958464035428252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6889631778474855617345989 1291805958464035428252373)
                ·
                  refine ⟨30276702151500830349665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1291805958464035428252373 30276702151500830349665)
                  ·
                    rfl

theorem cell23_530673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_530673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530673 prefixEnd_530673 := by exact prefixLift 530673
  have htrace : WordTrace (prefixWord ++ tailWord_530673) baseStart_530673 baseEnd_530673 := by
    simpa [prefixWord, tailWord_530673, baseEnd_530673] using wordTrace_append hprefix tailTrace_530673
  have hstable : (prefixWord ++ tailWord_530673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530673).length < 2 ^ (prefixWord ++ tailWord_530673).sum := by decide
  have hdescent : baseEnd_530673 < baseStart_530673 := by decide
  rcases family_descends (prefixWord ++ tailWord_530673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530700 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_530700 : Nat := 118140960795 + 530700 * 2 ^ 59
def prefixEnd_530700 : Nat := 4983230072969 + 3 ^ 40 * 530700 * 2
def baseEnd_530700 : Nat := 272504183341178867509361

theorem tailTrace_530700 : CollatzResearch.WordTrace tailWord_530700 prefixEnd_530700 272504183341178867509361 := by
  unfold tailWord_530700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9678109588686005594590777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12904146118248007459454369 9678109588686005594590777)
  ·
    refine ⟨7258582191514504195943083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9678109588686005594590777 7258582191514504195943083)
    ·
      refine ⟨10887873287271756293914625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7258582191514504195943083 10887873287271756293914625)
      ·
        refine ⟨8165904965453817220435969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10887873287271756293914625 8165904965453817220435969)
        ·
          refine ⟨6124428724090362915326977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8165904965453817220435969 6124428724090362915326977)
          ·
            refine ⟨4593321543067772186495233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6124428724090362915326977 4593321543067772186495233)
            ·
              refine ⟨3444991157300829139871425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593321543067772186495233 3444991157300829139871425)
              ·
                refine ⟨2583743367975621854903569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444991157300829139871425 2583743367975621854903569)
                ·
                  refine ⟨1937807525981716391177677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583743367975621854903569 1937807525981716391177677)
                  ·
                    refine ⟨726677822243143646691629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1937807525981716391177677 726677822243143646691629)
                    ·
                      refine ⟨272504183341178867509361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 726677822243143646691629 272504183341178867509361)
                      ·
                        rfl

theorem cell23_530700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_530700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530700 prefixEnd_530700 := by exact prefixLift 530700
  have htrace : WordTrace (prefixWord ++ tailWord_530700) baseStart_530700 baseEnd_530700 := by
    simpa [prefixWord, tailWord_530700, baseEnd_530700] using wordTrace_append hprefix tailTrace_530700
  have hstable : (prefixWord ++ tailWord_530700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530700).length < 2 ^ (prefixWord ++ tailWord_530700).sum := by decide
  have hdescent : baseEnd_530700 < baseStart_530700 := by decide
  rcases family_descends (prefixWord ++ tailWord_530700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530718 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_530718 : Nat := 118140960795 + 530718 * 2 ^ 59
def prefixEnd_530718 : Nat := 4983230072969 + 3 ^ 40 * 530718 * 2
def baseEnd_530718 : Nat := 272513425992959797084279

theorem tailTrace_530718 : CollatzResearch.WordTrace tailWord_530718 prefixEnd_530718 272513425992959797084279 := by
  unfold tailWord_530718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419609461413350032917101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12904583794204533508891205 2419609461413350032917101)
  ·
    refine ⟨907353548030006262343913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2419609461413350032917101 907353548030006262343913)
    ·
      refine ⟨680515161022504696757935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907353548030006262343913 680515161022504696757935)
      ·
        refine ⟨1020772741533757045136903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680515161022504696757935 1020772741533757045136903)
        ·
          refine ⟨1531159112300635567705355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020772741533757045136903 1531159112300635567705355)
          ·
            refine ⟨2296738668450953351558033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531159112300635567705355 2296738668450953351558033)
            ·
              refine ⟨1722554001338215013668525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296738668450953351558033 1722554001338215013668525)
              ·
                refine ⟨645957750501830630125697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722554001338215013668525 645957750501830630125697)
                ·
                  refine ⟨484468312876372972594273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645957750501830630125697 484468312876372972594273)
                  ·
                    refine ⟨363351234657279729445705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484468312876372972594273 363351234657279729445705)
                    ·
                      refine ⟨272513425992959797084279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363351234657279729445705 272513425992959797084279)
                      ·
                        rfl

theorem cell23_530718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_530718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530718 prefixEnd_530718 := by exact prefixLift 530718
  have htrace : WordTrace (prefixWord ++ tailWord_530718) baseStart_530718 baseEnd_530718 := by
    simpa [prefixWord, tailWord_530718, baseEnd_530718] using wordTrace_append hprefix tailTrace_530718
  have hstable : (prefixWord ++ tailWord_530718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530718).length < 2 ^ (prefixWord ++ tailWord_530718).sum := by decide
  have hdescent : baseEnd_530718 < baseStart_530718 := by decide
  rcases family_descends (prefixWord ++ tailWord_530718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530818 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_530818 : Nat := 118140960795 + 530818 * 2 ^ 59
def prefixEnd_530818 : Nat := 4983230072969 + 3 ^ 40 * 530818 * 2
def baseEnd_530818 : Nat := 90854924686136468611273

theorem tailTrace_530818 : CollatzResearch.WordTrace tailWord_530818 prefixEnd_530818 90854924686136468611273 := by
  unfold tailWord_530818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840130747736129335494277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12907015327296344894651405 4840130747736129335494277)
  ·
    refine ⟨907524515200524250405177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4840130747736129335494277 907524515200524250405177)
    ·
      refine ⟨680643386400393187803883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907524515200524250405177 680643386400393187803883)
      ·
        refine ⟨1020965079600589781705825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680643386400393187803883 1020965079600589781705825)
        ·
          refine ⟨765723809700442336279369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020965079600589781705825 765723809700442336279369)
          ·
            refine ⟨574292857275331752209527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765723809700442336279369 574292857275331752209527)
            ·
              refine ⟨861439285912997628314291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574292857275331752209527 861439285912997628314291)
              ·
                refine ⟨1292158928869496442471437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861439285912997628314291 1292158928869496442471437)
                ·
                  refine ⟨484559598326061165926789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1292158928869496442471437 484559598326061165926789)
                  ·
                    refine ⟨90854924686136468611273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484559598326061165926789 90854924686136468611273)
                    ·
                      rfl

theorem cell23_530818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_530818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530818 prefixEnd_530818 := by exact prefixLift 530818
  have htrace : WordTrace (prefixWord ++ tailWord_530818) baseStart_530818 baseEnd_530818 := by
    simpa [prefixWord, tailWord_530818, baseEnd_530818] using wordTrace_append hprefix tailTrace_530818
  have hstable : (prefixWord ++ tailWord_530818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530818).length < 2 ^ (prefixWord ++ tailWord_530818).sum := by decide
  have hdescent : baseEnd_530818 < baseStart_530818 := by decide
  rcases family_descends (prefixWord ++ tailWord_530818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530847 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_530847 : Nat := 118140960795 + 530847 * 2 ^ 59
def prefixEnd_530847 : Nat := 4983230072969 + 3 ^ 40 * 530847 * 2
def baseEnd_530847 : Nat := 272579664997389792371185

theorem tailTrace_530847 : CollatzResearch.WordTrace tailWord_530847 prefixEnd_530847 272579664997389792371185 := by
  unfold tailWord_530847
  simp only [CollatzResearch.WordTrace]
  refine ⟨19361580707839455294782795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12907720471892970196521863 19361580707839455294782795)
  ·
    refine ⟨29042371061759182942174193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19361580707839455294782795 29042371061759182942174193)
    ·
      refine ⟨21781778296319387206630645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29042371061759182942174193 21781778296319387206630645)
      ·
        refine ⟨2042041715279942550621623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21781778296319387206630645 2042041715279942550621623)
        ·
          refine ⟨3063062572919913825932435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042041715279942550621623 3063062572919913825932435)
          ·
            refine ⟨4594593859379870738898653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063062572919913825932435 4594593859379870738898653)
            ·
              refine ⟨1722972697267451527086995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4594593859379870738898653 1722972697267451527086995)
              ·
                refine ⟨2584459045901177290630493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722972697267451527086995 2584459045901177290630493)
                ·
                  refine ⟨969172142212941483986435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2584459045901177290630493 969172142212941483986435)
                  ·
                    refine ⟨1453758213319412225979653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969172142212941483986435 1453758213319412225979653)
                    ·
                      refine ⟨272579664997389792371185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1453758213319412225979653 272579664997389792371185)
                      ·
                        rfl

theorem cell23_530847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_530847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530847 prefixEnd_530847 := by exact prefixLift 530847
  have htrace : WordTrace (prefixWord ++ tailWord_530847) baseStart_530847 baseEnd_530847 := by
    simpa [prefixWord, tailWord_530847, baseEnd_530847] using wordTrace_append hprefix tailTrace_530847
  have hstable : (prefixWord ++ tailWord_530847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530847).length < 2 ^ (prefixWord ++ tailWord_530847).sum := by decide
  have hdescent : baseEnd_530847 < baseStart_530847 := by decide
  rcases family_descends (prefixWord ++ tailWord_530847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530870 : List Nat := [5, 1, 17]
def baseStart_530870 : Nat := 118140960795 + 530870 * 2 ^ 59
def prefixEnd_530870 : Nat := 4983230072969 + 3 ^ 40 * 530870 * 2
def baseEnd_530870 : Nat := 41547245092583935739

theorem tailTrace_530870 : CollatzResearch.WordTrace tailWord_530870 prefixEnd_530870 41547245092583935739 := by
  unfold tailWord_530870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210151224172258138929379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12908279724504086815246709 1210151224172258138929379)
  ·
    refine ⟨1815226836258387208394069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1210151224172258138929379 1815226836258387208394069)
    ·
      refine ⟨41547245092583935739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 1815226836258387208394069 41547245092583935739)
      ·
        rfl

theorem cell23_530870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 17].length) (baseStart_530870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530870 prefixEnd_530870 := by exact prefixLift 530870
  have htrace : WordTrace (prefixWord ++ tailWord_530870) baseStart_530870 baseEnd_530870 := by
    simpa [prefixWord, tailWord_530870, baseEnd_530870] using wordTrace_append hprefix tailTrace_530870
  have hstable : (prefixWord ++ tailWord_530870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530870).length < 2 ^ (prefixWord ++ tailWord_530870).sum := by decide
  have hdescent : baseEnd_530870 < baseStart_530870 := by decide
  rcases family_descends (prefixWord ++ tailWord_530870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530887 : List Nat := [1, 1, 4, 1, 1, 6, 1, 8]
def baseStart_530887 : Nat := 118140960795 + 530887 * 2 ^ 59
def prefixEnd_530887 : Nat := 4983230072969 + 3 ^ 40 * 530887 * 2
def baseEnd_530887 : Nat := 10096303860132208735963

theorem tailTrace_530887 : CollatzResearch.WordTrace tailWord_530887 prefixEnd_530887 10096303860132208735963 := by
  unfold tailWord_530887
  simp only [CollatzResearch.WordTrace]
  refine ⟨19363039627694542126238915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12908693085129694750825943 19363039627694542126238915)
  ·
    refine ⟨29044559441541813189358373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19363039627694542126238915 29044559441541813189358373)
    ·
      refine ⟨5445854895289089973004695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29044559441541813189358373 5445854895289089973004695)
      ·
        refine ⟨8168782342933634959507043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5445854895289089973004695 8168782342933634959507043)
        ·
          refine ⟨12253173514400452439260565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168782342933634959507043 12253173514400452439260565)
          ·
            refine ⟨574367508487521208090339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12253173514400452439260565 574367508487521208090339)
            ·
              refine ⟨861551262731281812135509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574367508487521208090339 861551262731281812135509)
              ·
                refine ⟨10096303860132208735963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 861551262731281812135509 10096303860132208735963)
                ·
                  rfl

theorem cell23_530887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 8].length) (baseStart_530887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530887 prefixEnd_530887 := by exact prefixLift 530887
  have htrace : WordTrace (prefixWord ++ tailWord_530887) baseStart_530887 baseEnd_530887 := by
    simpa [prefixWord, tailWord_530887, baseEnd_530887] using wordTrace_append hprefix tailTrace_530887
  have hstable : (prefixWord ++ tailWord_530887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530887).length < 2 ^ (prefixWord ++ tailWord_530887).sum := by decide
  have hdescent : baseEnd_530887 < baseStart_530887 := by decide
  rcases family_descends (prefixWord ++ tailWord_530887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530915 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 1, 2, 2]
def baseStart_530915 : Nat := 118140960795 + 530915 * 2 ^ 59
def prefixEnd_530915 : Nat := 4983230072969 + 3 ^ 40 * 530915 * 2
def baseEnd_530915 : Nat := 272614581681895526320873

theorem tailTrace_530915 : CollatzResearch.WordTrace tailWord_530915 prefixEnd_530915 272614581681895526320873 := by
  unfold tailWord_530915
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364060871593102908258199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12909373914395401938838799 19364060871593102908258199)
  ·
    refine ⟨29046091307389654362387299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19364060871593102908258199 29046091307389654362387299)
    ·
      refine ⟨43569136961084481543580949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29046091307389654362387299 43569136961084481543580949)
      ·
        refine ⟨2042303295050835072355357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43569136961084481543580949 2042303295050835072355357)
        ·
          refine ⟨765863735644063152133259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2042303295050835072355357 765863735644063152133259)
          ·
            refine ⟨1148795603466094728199889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765863735644063152133259 1148795603466094728199889)
            ·
              refine ⟨861596702599571046149917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148795603466094728199889 861596702599571046149917)
              ·
                refine ⟨323098763474839142306219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861596702599571046149917 323098763474839142306219)
                ·
                  refine ⟨484648145212258713459329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323098763474839142306219 484648145212258713459329)
                  ·
                    refine ⟨363486108909194035094497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484648145212258713459329 363486108909194035094497)
                    ·
                      refine ⟨272614581681895526320873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363486108909194035094497 272614581681895526320873)
                      ·
                        rfl

theorem cell23_530915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_530915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530915 prefixEnd_530915 := by exact prefixLift 530915
  have htrace : WordTrace (prefixWord ++ tailWord_530915) baseStart_530915 baseEnd_530915 := by
    simpa [prefixWord, tailWord_530915, baseEnd_530915] using wordTrace_append hprefix tailTrace_530915
  have hstable : (prefixWord ++ tailWord_530915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530915).length < 2 ^ (prefixWord ++ tailWord_530915).sum := by decide
  have hdescent : baseEnd_530915 < baseStart_530915 := by decide
  rcases family_descends (prefixWord ++ tailWord_530915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530958 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_530958 : Nat := 118140960795 + 530958 * 2 ^ 59
def prefixEnd_530958 : Nat := 4983230072969 + 3 ^ 40 * 530958 * 2
def baseEnd_530958 : Nat := 272636661350038858083175

theorem tailTrace_530958 : CollatzResearch.WordTrace tailWord_530958 prefixEnd_530958 272636661350038858083175 := by
  unfold tailWord_530958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420703651304665156509191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12910419473624880834715685 2420703651304665156509191)
  ·
    refine ⟨3631055476956997734763787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420703651304665156509191 3631055476956997734763787)
    ·
      refine ⟨5446583215435496602145681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631055476956997734763787 5446583215435496602145681)
      ·
        refine ⟨4084937411576622451609261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5446583215435496602145681 4084937411576622451609261)
        ·
          refine ⟨1531851529341233419353473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4084937411576622451609261 1531851529341233419353473)
          ·
            refine ⟨1148888647005925064515105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531851529341233419353473 1148888647005925064515105)
            ·
              refine ⟨861666485254443798386329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148888647005925064515105 861666485254443798386329)
              ·
                refine ⟨646249863940832848789747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861666485254443798386329 646249863940832848789747)
                ·
                  refine ⟨969374795911249273184621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646249863940832848789747 969374795911249273184621)
                  ·
                    refine ⟨363515548466718477444233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969374795911249273184621 363515548466718477444233)
                    ·
                      refine ⟨272636661350038858083175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363515548466718477444233 272636661350038858083175)
                      ·
                        rfl

theorem cell23_530958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_530958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530958 prefixEnd_530958 := by exact prefixLift 530958
  have htrace : WordTrace (prefixWord ++ tailWord_530958) baseStart_530958 baseEnd_530958 := by
    simpa [prefixWord, tailWord_530958, baseEnd_530958] using wordTrace_append hprefix tailTrace_530958
  have hstable : (prefixWord ++ tailWord_530958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530958).length < 2 ^ (prefixWord ++ tailWord_530958).sum := by decide
  have hdescent : baseEnd_530958 < baseStart_530958 := by decide
  rcases family_descends (prefixWord ++ tailWord_530958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530960 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 13]
def baseStart_530960 : Nat := 118140960795 + 530960 * 2 ^ 59
def prefixEnd_530960 : Nat := 4983230072969 + 3 ^ 40 * 530960 * 2
def baseEnd_530960 : Nat := 30293076479038650028685

theorem tailTrace_530960 : CollatzResearch.WordTrace tailWord_530960 prefixEnd_530960 30293076479038650028685 := by
  unfold tailWord_530960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682851078215037796823167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12910468104286717062430889 9682851078215037796823167)
  ·
    refine ⟨14524276617322556695234751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9682851078215037796823167 14524276617322556695234751)
    ·
      refine ⟨21786414925983835042852127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14524276617322556695234751 21786414925983835042852127)
      ·
        refine ⟨32679622388975752564278191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21786414925983835042852127 32679622388975752564278191)
        ·
          refine ⟨49019433583463628846417287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32679622388975752564278191 49019433583463628846417287)
          ·
            refine ⟨73529150375195443269625931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49019433583463628846417287 73529150375195443269625931)
            ·
              refine ⟨110293725562793164904438897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73529150375195443269625931 110293725562793164904438897)
              ·
                refine ⟨82720294172094873678329173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110293725562793164904438897 82720294172094873678329173)
                ·
                  refine ⟨30293076479038650028685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 82720294172094873678329173 30293076479038650028685)
                  ·
                    rfl

theorem cell23_530960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_530960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530960 prefixEnd_530960 := by exact prefixLift 530960
  have htrace : WordTrace (prefixWord ++ tailWord_530960) baseStart_530960 baseEnd_530960 := by
    simpa [prefixWord, tailWord_530960, baseEnd_530960] using wordTrace_append hprefix tailTrace_530960
  have hstable : (prefixWord ++ tailWord_530960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530960).length < 2 ^ (prefixWord ++ tailWord_530960).sum := by decide
  have hdescent : baseEnd_530960 < baseStart_530960 := by decide
  rcases family_descends (prefixWord ++ tailWord_530960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530987 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3]
def baseStart_530987 : Nat := 118140960795 + 530987 * 2 ^ 59
def prefixEnd_530987 : Nat := 4983230072969 + 3 ^ 40 * 530987 * 2
def baseEnd_530987 : Nat := 272651552289019244620541

theorem tailTrace_530987 : CollatzResearch.WordTrace tailWord_530987 prefixEnd_530987 272651552289019244620541 := by
  unfold tailWord_530987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19366686927332259204879215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12911124618221506136586143 19366686927332259204879215)
  ·
    refine ⟨29050030390998388807318823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19366686927332259204879215 29050030390998388807318823)
    ·
      refine ⟨43575045586497583210978235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29050030390998388807318823 43575045586497583210978235)
      ·
        refine ⟨65362568379746374816467353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43575045586497583210978235 65362568379746374816467353)
        ·
          refine ⟨49021926284809781112350515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65362568379746374816467353 49021926284809781112350515)
          ·
            refine ⟨73532889427214671668525773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49021926284809781112350515 73532889427214671668525773)
            ·
              refine ⟨27574833535205501875697165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73532889427214671668525773 27574833535205501875697165)
              ·
                refine ⟨10340562575702063203386437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27574833535205501875697165 10340562575702063203386437)
                ·
                  refine ⟨1938855482944136850634957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10340562575702063203386437 1938855482944136850634957)
                  ·
                    refine ⟨727070806104051318988109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938855482944136850634957 727070806104051318988109)
                    ·
                      refine ⟨272651552289019244620541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727070806104051318988109 272651552289019244620541)
                      ·
                        rfl

theorem cell23_530987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].length) (baseStart_530987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530987 prefixEnd_530987 := by exact prefixLift 530987
  have htrace : WordTrace (prefixWord ++ tailWord_530987) baseStart_530987 baseEnd_530987 := by
    simpa [prefixWord, tailWord_530987, baseEnd_530987] using wordTrace_append hprefix tailTrace_530987
  have hstable : (prefixWord ++ tailWord_530987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530987).length < 2 ^ (prefixWord ++ tailWord_530987).sum := by decide
  have hdescent : baseEnd_530987 < baseStart_530987 := by decide
  rcases family_descends (prefixWord ++ tailWord_530987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_530994 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_530994 : Nat := 118140960795 + 530994 * 2 ^ 59
def prefixEnd_530994 : Nat := 4983230072969 + 3 ^ 40 * 530994 * 2
def baseEnd_530994 : Nat := 30295016294844524137001

theorem tailTrace_530994 : CollatzResearch.WordTrace tailWord_530994 prefixEnd_530994 30295016294844524137001 := by
  unfold tailWord_530994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841735559576724850096009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12911294825537932933589357 4841735559576724850096009)
  ·
    refine ⟨3631301669682543637572007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841735559576724850096009 3631301669682543637572007)
    ·
      refine ⟨5446952504523815456358011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631301669682543637572007 5446952504523815456358011)
      ·
        refine ⟨8170428756785723184537017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446952504523815456358011 8170428756785723184537017)
        ·
          refine ⟨6127821567589292388402763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8170428756785723184537017 6127821567589292388402763)
          ·
            refine ⟨9191732351383938582604145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127821567589292388402763 9191732351383938582604145)
            ·
              refine ⟨6893799263537953936953109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9191732351383938582604145 6893799263537953936953109)
              ·
                refine ⟨323146840478341590794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6893799263537953936953109 323146840478341590794677)
                ·
                  refine ⟨30295016294844524137001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323146840478341590794677 30295016294844524137001)
                  ·
                    rfl

theorem cell23_530994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_530994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_530994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_530994 prefixEnd_530994 := by exact prefixLift 530994
  have htrace : WordTrace (prefixWord ++ tailWord_530994) baseStart_530994 baseEnd_530994 := by
    simpa [prefixWord, tailWord_530994, baseEnd_530994] using wordTrace_append hprefix tailTrace_530994
  have hstable : (prefixWord ++ tailWord_530994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_530994).length < 2 ^ (prefixWord ++ tailWord_530994).sum := by decide
  have hdescent : baseEnd_530994 < baseStart_530994 := by decide
  rcases family_descends (prefixWord ++ tailWord_530994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531005 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 2, 2, 2]
def baseStart_531005 : Nat := 118140960795 + 531005 * 2 ^ 59
def prefixEnd_531005 : Nat := 4983230072969 + 3 ^ 40 * 531005 * 2
def baseEnd_531005 : Nat := 272660794940800174195459

theorem tailTrace_531005 : CollatzResearch.WordTrace tailWord_531005 prefixEnd_531005 272660794940800174195459 := by
  unfold tailWord_531005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367343441267048279034469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12911562294178032186022979 19367343441267048279034469)
  ·
    refine ⟨3631376895237571552318963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19367343441267048279034469 3631376895237571552318963)
    ·
      refine ⟨5447065342856357328478445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631376895237571552318963 5447065342856357328478445)
      ·
        refine ⟨2042649503571133998179417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5447065342856357328478445 2042649503571133998179417)
        ·
          refine ⟨1531987127678350498634563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2042649503571133998179417 1531987127678350498634563)
          ·
            refine ⟨2297980691517525747951845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531987127678350498634563 2297980691517525747951845)
            ·
              refine ⟨430871379659536077740971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2297980691517525747951845 430871379659536077740971)
              ·
                refine ⟨646307069489304116611457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430871379659536077740971 646307069489304116611457)
                ·
                  refine ⟨484730302116978087458593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646307069489304116611457 484730302116978087458593)
                  ·
                    refine ⟨363547726587733565593945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484730302116978087458593 363547726587733565593945)
                    ·
                      refine ⟨272660794940800174195459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363547726587733565593945 272660794940800174195459)
                      ·
                        rfl

theorem cell23_531005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_531005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531005 prefixEnd_531005 := by exact prefixLift 531005
  have htrace : WordTrace (prefixWord ++ tailWord_531005) baseStart_531005 baseEnd_531005 := by
    simpa [prefixWord, tailWord_531005, baseEnd_531005] using wordTrace_append hprefix tailTrace_531005
  have hstable : (prefixWord ++ tailWord_531005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531005).length < 2 ^ (prefixWord ++ tailWord_531005).sum := by decide
  have hdescent : baseEnd_531005 < baseStart_531005 := by decide
  rcases family_descends (prefixWord ++ tailWord_531005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531007 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 4, 5]
def baseStart_531007 : Nat := 118140960795 + 531007 * 2 ^ 59
def prefixEnd_531007 : Nat := 4983230072969 + 3 ^ 40 * 531007 * 2
def baseEnd_531007 : Nat := 90887273967369722123483

theorem tailTrace_531007 : CollatzResearch.WordTrace tailWord_531007 prefixEnd_531007 90887273967369722123483 := by
  unfold tailWord_531007
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367416387259802620607275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12911610924839868413738183 19367416387259802620607275)
  ·
    refine ⟨29051124580889703930910913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19367416387259802620607275 29051124580889703930910913)
    ·
      refine ⟨21788343435667277948183185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29051124580889703930910913 21788343435667277948183185)
      ·
        refine ⟨16341257576750458461137389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21788343435667277948183185 16341257576750458461137389)
        ·
          refine ⟨6127971591281421922926521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16341257576750458461137389 6127971591281421922926521)
          ·
            refine ⟨4595978693461066442194891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6127971591281421922926521 4595978693461066442194891)
            ·
              refine ⟨6893968040191599663292337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595978693461066442194891 6893968040191599663292337)
              ·
                refine ⟨5170476030143699747469253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6893968040191599663292337 5170476030143699747469253)
                ·
                  refine ⟨969464255651943702650485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5170476030143699747469253 969464255651943702650485)
                  ·
                    refine ⟨90887273967369722123483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 969464255651943702650485 90887273967369722123483)
                    ·
                      rfl

theorem cell23_531007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_531007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531007 prefixEnd_531007 := by exact prefixLift 531007
  have htrace : WordTrace (prefixWord ++ tailWord_531007) baseStart_531007 baseEnd_531007 := by
    simpa [prefixWord, tailWord_531007, baseEnd_531007] using wordTrace_append hprefix tailTrace_531007
  have hstable : (prefixWord ++ tailWord_531007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531007).length < 2 ^ (prefixWord ++ tailWord_531007).sum := by decide
  have hdescent : baseEnd_531007 < baseStart_531007 := by decide
  rcases family_descends (prefixWord ++ tailWord_531007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531044 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_531044 : Nat := 118140960795 + 531044 * 2 ^ 59
def prefixEnd_531044 : Nat := 4983230072969 + 3 ^ 40 * 531044 * 2
def baseEnd_531044 : Nat := 272680820686325521607779

theorem tailTrace_531044 : CollatzResearch.WordTrace tailWord_531044 prefixEnd_531044 272680820686325521607779 := by
  unfold tailWord_531044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684382944062878969852093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12912510592083838626469457 9684382944062878969852093)
  ·
    refine ⟨3631643604023579613694535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9684382944062878969852093 3631643604023579613694535)
    ·
      refine ⟨5447465406035369420541803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631643604023579613694535 5447465406035369420541803)
      ·
        refine ⟨8171198109053054130812705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447465406035369420541803 8171198109053054130812705)
        ·
          refine ⟨6128398581789790598109529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8171198109053054130812705 6128398581789790598109529)
          ·
            refine ⟨4596298936342342948582147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6128398581789790598109529 4596298936342342948582147)
            ·
              refine ⟨6894448404513514422873221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596298936342342948582147 6894448404513514422873221)
              ·
                refine ⟨1292709075846283954288729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6894448404513514422873221 1292709075846283954288729)
                ·
                  refine ⟨969531806884712965716547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292709075846283954288729 969531806884712965716547)
                  ·
                    refine ⟨1454297710327069448574821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969531806884712965716547 1454297710327069448574821)
                    ·
                      refine ⟨272680820686325521607779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1454297710327069448574821 272680820686325521607779)
                      ·
                        rfl

theorem cell23_531044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_531044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531044 prefixEnd_531044 := by exact prefixLift 531044
  have htrace : WordTrace (prefixWord ++ tailWord_531044) baseStart_531044 baseEnd_531044 := by
    simpa [prefixWord, tailWord_531044, baseEnd_531044] using wordTrace_append hprefix tailTrace_531044
  have hstable : (prefixWord ++ tailWord_531044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531044).length < 2 ^ (prefixWord ++ tailWord_531044).sum := by decide
  have hdescent : baseEnd_531044 < baseStart_531044 := by decide
  rcases family_descends (prefixWord ++ tailWord_531044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531045 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 5]
def baseStart_531045 : Nat := 118140960795 + 531045 * 2 ^ 59
def prefixEnd_531045 : Nat := 4983230072969 + 3 ^ 40 * 531045 * 2
def baseEnd_531045 : Nat := 30297926018553335299475

theorem tailTrace_531045 : CollatzResearch.WordTrace tailWord_531045 prefixEnd_531045 30297926018553335299475 := by
  unfold tailWord_531045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368802361122135110490589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12912534907414756740327059 19368802361122135110490589)
  ·
    refine ⟨7263300885420800666433971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19368802361122135110490589 7263300885420800666433971)
    ·
      refine ⟨10894951328131200999650957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263300885420800666433971 10894951328131200999650957)
      ·
        refine ⟨4085606748049200374869109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10894951328131200999650957 4085606748049200374869109)
        ·
          refine ⟨383025632629612535143979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4085606748049200374869109 383025632629612535143979)
          ·
            refine ⟨574538448944418802715969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383025632629612535143979 574538448944418802715969)
            ·
              refine ⟨430903836708314102036977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574538448944418802715969 430903836708314102036977)
              ·
                refine ⟨323177877531235576527733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430903836708314102036977 323177877531235576527733)
                ·
                  refine ⟨30297926018553335299475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323177877531235576527733 30297926018553335299475)
                  ·
                    rfl

theorem cell23_531045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_531045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531045 prefixEnd_531045 := by exact prefixLift 531045
  have htrace : WordTrace (prefixWord ++ tailWord_531045) baseStart_531045 baseEnd_531045 := by
    simpa [prefixWord, tailWord_531045, baseEnd_531045] using wordTrace_append hprefix tailTrace_531045
  have hstable : (prefixWord ++ tailWord_531045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531045).length < 2 ^ (prefixWord ++ tailWord_531045).sum := by decide
  have hdescent : baseEnd_531045 < baseStart_531045 := by decide
  rcases family_descends (prefixWord ++ tailWord_531045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531047 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_531047 : Nat := 118140960795 + 531047 * 2 ^ 59
def prefixEnd_531047 : Nat := 4983230072969 + 3 ^ 40 * 531047 * 2
def baseEnd_531047 : Nat := 272682361128289009870265

theorem tailTrace_531047 : CollatzResearch.WordTrace tailWord_531047 prefixEnd_531047 272682361128289009870265 := by
  unfold tailWord_531047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368875307114889452063395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12912583538076592968042263 19368875307114889452063395)
  ·
    refine ⟨29053312960672334178095093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19368875307114889452063395 29053312960672334178095093)
    ·
      refine ⟨2723748090063031329196415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29053312960672334178095093 2723748090063031329196415)
      ·
        refine ⟨4085622135094546993794623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723748090063031329196415 4085622135094546993794623)
        ·
          refine ⟨6128433202641820490691935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085622135094546993794623 6128433202641820490691935)
          ·
            refine ⟨9192649803962730736037903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128433202641820490691935 9192649803962730736037903)
            ·
              refine ⟨13788974705944096104056855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9192649803962730736037903 13788974705944096104056855)
              ·
                refine ⟨20683462058916144156085283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13788974705944096104056855 20683462058916144156085283)
                ·
                  refine ⟨31025193088374216234127925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20683462058916144156085283 31025193088374216234127925)
                  ·
                    refine ⟨2908611852035082771949493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31025193088374216234127925 2908611852035082771949493)
                    ·
                      refine ⟨272682361128289009870265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2908611852035082771949493 272682361128289009870265)
                      ·
                        rfl

theorem cell23_531047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_531047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531047 prefixEnd_531047 := by exact prefixLift 531047
  have htrace : WordTrace (prefixWord ++ tailWord_531047) baseStart_531047 baseEnd_531047 := by
    simpa [prefixWord, tailWord_531047, baseEnd_531047] using wordTrace_append hprefix tailTrace_531047
  have hstable : (prefixWord ++ tailWord_531047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531047).length < 2 ^ (prefixWord ++ tailWord_531047).sum := by decide
  have hdescent : baseEnd_531047 < baseStart_531047 := by decide
  rcases family_descends (prefixWord ++ tailWord_531047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531057 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_531057 : Nat := 118140960795 + 531057 * 2 ^ 59
def prefixEnd_531057 : Nat := 4983230072969 + 3 ^ 40 * 531057 * 2
def baseEnd_531057 : Nat := 272687495934833970745219

theorem tailTrace_531057 : CollatzResearch.WordTrace tailWord_531057 prefixEnd_531057 272687495934833970745219 := by
  unfold tailWord_531057
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369240037078661159927425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12912826691385774106618283 19369240037078661159927425)
  ·
    refine ⟨14526930027808995869945569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19369240037078661159927425 14526930027808995869945569)
    ·
      refine ⟨10895197520856746902459177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14526930027808995869945569 10895197520856746902459177)
      ·
        refine ⟨8171398140642560176844383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10895197520856746902459177 8171398140642560176844383)
        ·
          refine ⟨12257097210963840265266575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171398140642560176844383 12257097210963840265266575)
          ·
            refine ⟨18385645816445760397899863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257097210963840265266575 18385645816445760397899863)
            ·
              refine ⟨27578468724668640596849795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18385645816445760397899863 27578468724668640596849795)
              ·
                refine ⟨41367703087002960895274693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27578468724668640596849795 41367703087002960895274693)
                ·
                  refine ⟨7756444328813055167864005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41367703087002960895274693 7756444328813055167864005)
                  ·
                    refine ⟨1454333311652447843974501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7756444328813055167864005 1454333311652447843974501)
                    ·
                      refine ⟨272687495934833970745219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1454333311652447843974501 272687495934833970745219)
                      ·
                        rfl

theorem cell23_531057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_531057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531057 prefixEnd_531057 := by exact prefixLift 531057
  have htrace : WordTrace (prefixWord ++ tailWord_531057) baseStart_531057 baseEnd_531057 := by
    simpa [prefixWord, tailWord_531057, baseEnd_531057] using wordTrace_append hprefix tailTrace_531057
  have hstable : (prefixWord ++ tailWord_531057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531057).length < 2 ^ (prefixWord ++ tailWord_531057).sum := by decide
  have hdescent : baseEnd_531057 < baseStart_531057 := by decide
  rcases family_descends (prefixWord ++ tailWord_531057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531107 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_531107 : Nat := 118140960795 + 531107 * 2 ^ 59
def prefixEnd_531107 : Nat := 4983230072969 + 3 ^ 40 * 531107 * 2
def baseEnd_531107 : Nat := 272713169967558775119989

theorem tailTrace_531107 : CollatzResearch.WordTrace tailWord_531107 prefixEnd_531107 272713169967558775119989 := by
  unfold tailWord_531107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19371063686897519699247575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12914042457931679799498383 19371063686897519699247575)
  ·
    refine ⟨29056595530346279548871363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19371063686897519699247575 29056595530346279548871363)
    ·
      refine ⟨43584893295519419323307045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29056595530346279548871363 43584893295519419323307045)
      ·
        refine ⟨8172167492909891123120071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43584893295519419323307045 8172167492909891123120071)
        ·
          refine ⟨12258251239364836684680107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8172167492909891123120071 12258251239364836684680107)
          ·
            refine ⟨18387376859047255027020161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12258251239364836684680107 18387376859047255027020161)
            ·
              refine ⟨13790532644285441270265121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18387376859047255027020161 13790532644285441270265121)
              ·
                refine ⟨10342899483214080952698841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13790532644285441270265121 10342899483214080952698841)
                ·
                  refine ⟨7757174612410560714524131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10342899483214080952698841 7757174612410560714524131)
                  ·
                    refine ⟨11635761918615841071786197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7757174612410560714524131 11635761918615841071786197)
                    ·
                      refine ⟨272713169967558775119989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11635761918615841071786197 272713169967558775119989)
                      ·
                        rfl

theorem cell23_531107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_531107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531107 prefixEnd_531107 := by exact prefixLift 531107
  have htrace : WordTrace (prefixWord ++ tailWord_531107) baseStart_531107 baseEnd_531107 := by
    simpa [prefixWord, tailWord_531107, baseEnd_531107] using wordTrace_append hprefix tailTrace_531107
  have hstable : (prefixWord ++ tailWord_531107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531107).length < 2 ^ (prefixWord ++ tailWord_531107).sum := by decide
  have hdescent : baseEnd_531107 < baseStart_531107 := by decide
  rcases family_descends (prefixWord ++ tailWord_531107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531161 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_531161 : Nat := 118140960795 + 531161 * 2 ^ 59
def prefixEnd_531161 : Nat := 4983230072969 + 3 ^ 40 * 531161 * 2
def baseEnd_531161 : Nat := 90913632640967187948247

theorem tailTrace_531161 : CollatzResearch.WordTrace tailWord_531161 prefixEnd_531161 90913632640967187948247 := by
  unfold tailWord_531161
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373033228701886921713337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12915355485801257947808891 19373033228701886921713337)
  ·
    refine ⟨14529774921526415191285003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19373033228701886921713337 14529774921526415191285003)
    ·
      refine ⟨21794662382289622786927505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14529774921526415191285003 21794662382289622786927505)
      ·
        refine ⟨16345996786717217090195629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21794662382289622786927505 16345996786717217090195629)
        ·
          refine ⟨6129748795018956408823361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16345996786717217090195629 6129748795018956408823361)
          ·
            refine ⟨4597311596264217306617521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129748795018956408823361 4597311596264217306617521)
            ·
              refine ⟨3447983697198162979963141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597311596264217306617521 3447983697198162979963141)
              ·
                refine ⟨646496943224655558743089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3447983697198162979963141 646496943224655558743089)
                ·
                  refine ⟨484872707418491669057317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646496943224655558743089 484872707418491669057317)
                  ·
                    refine ⟨90913632640967187948247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 484872707418491669057317 90913632640967187948247)
                    ·
                      rfl

theorem cell23_531161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_531161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531161 prefixEnd_531161 := by exact prefixLift 531161
  have htrace : WordTrace (prefixWord ++ tailWord_531161) baseStart_531161 baseEnd_531161 := by
    simpa [prefixWord, tailWord_531161, baseEnd_531161] using wordTrace_append hprefix tailTrace_531161
  have hstable : (prefixWord ++ tailWord_531161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531161).length < 2 ^ (prefixWord ++ tailWord_531161).sum := by decide
  have hdescent : baseEnd_531161 < baseStart_531161 := by decide
  rcases family_descends (prefixWord ++ tailWord_531161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531171 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5]
def baseStart_531171 : Nat := 118140960795 + 531171 * 2 ^ 59
def prefixEnd_531171 : Nat := 4983230072969 + 3 ^ 40 * 531171 * 2
def baseEnd_531171 : Nat := 272746032729446524719695

theorem tailTrace_531171 : CollatzResearch.WordTrace tailWord_531171 prefixEnd_531171 272746032729446524719695 := by
  unfold tailWord_531171
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373397958665658629577367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12915598639110439086384911 19373397958665658629577367)
  ·
    refine ⟨29060096937998487944366051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19373397958665658629577367 29060096937998487944366051)
    ·
      refine ⟨43590145406997731916549077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29060096937998487944366051 43590145406997731916549077)
      ·
        refine ⟨1021644032976509341794119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43590145406997731916549077 1021644032976509341794119)
        ·
          refine ⟨1532466049464764012691179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021644032976509341794119 1532466049464764012691179)
          ·
            refine ⟨2298699074197146019036769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532466049464764012691179 2298699074197146019036769)
            ·
              refine ⟨1724024305647859514277577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298699074197146019036769 1724024305647859514277577)
              ·
                refine ⟨1293018229235894635708183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724024305647859514277577 1293018229235894635708183)
                ·
                  refine ⟨1939527343853841953562275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293018229235894635708183 1939527343853841953562275)
                  ·
                    refine ⟨2909291015780762930343413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939527343853841953562275 2909291015780762930343413)
                    ·
                      refine ⟨272746032729446524719695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2909291015780762930343413 272746032729446524719695)
                      ·
                        rfl

theorem cell23_531171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_531171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531171 prefixEnd_531171 := by exact prefixLift 531171
  have htrace : WordTrace (prefixWord ++ tailWord_531171) baseStart_531171 baseEnd_531171 := by
    simpa [prefixWord, tailWord_531171, baseEnd_531171] using wordTrace_append hprefix tailTrace_531171
  have hstable : (prefixWord ++ tailWord_531171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531171).length < 2 ^ (prefixWord ++ tailWord_531171).sum := by decide
  have hdescent : baseEnd_531171 < baseStart_531171 := by decide
  rcases family_descends (prefixWord ++ tailWord_531171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531181 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_531181 : Nat := 118140960795 + 531181 * 2 ^ 59
def prefixEnd_531181 : Nat := 4983230072969 + 3 ^ 40 * 531181 * 2
def baseEnd_531181 : Nat := 272751167535991485594649

theorem tailTrace_531181 : CollatzResearch.WordTrace tailWord_531181 prefixEnd_531181 272751167535991485594649 := by
  unfold tailWord_531181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373762688629430337441397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12915841792419620224960931 19373762688629430337441397)
  ·
    refine ⟨1816290252059009094135131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19373762688629430337441397 1816290252059009094135131)
    ·
      refine ⟨2724435378088513641202697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816290252059009094135131 2724435378088513641202697)
      ·
        refine ⟨2043326533566385230902023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2724435378088513641202697 2043326533566385230902023)
        ·
          refine ⟨3064989800349577846353035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043326533566385230902023 3064989800349577846353035)
          ·
            refine ⟨4597484700524366769529553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064989800349577846353035 4597484700524366769529553)
            ·
              refine ⟨3448113525393275077147165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597484700524366769529553 3448113525393275077147165)
              ·
                refine ⟨1293042572022478153930187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3448113525393275077147165 1293042572022478153930187)
                ·
                  refine ⟨1939563858033717230895281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293042572022478153930187 1939563858033717230895281)
                  ·
                    refine ⟨1454672893525287923171461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939563858033717230895281 1454672893525287923171461)
                    ·
                      refine ⟨272751167535991485594649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1454672893525287923171461 272751167535991485594649)
                      ·
                        rfl

theorem cell23_531181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_531181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531181 prefixEnd_531181 := by exact prefixLift 531181
  have htrace : WordTrace (prefixWord ++ tailWord_531181) baseStart_531181 baseEnd_531181 := by
    simpa [prefixWord, tailWord_531181, baseEnd_531181] using wordTrace_append hprefix tailTrace_531181
  have hstable : (prefixWord ++ tailWord_531181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531181).length < 2 ^ (prefixWord ++ tailWord_531181).sum := by decide
  have hdescent : baseEnd_531181 < baseStart_531181 := by decide
  rcases family_descends (prefixWord ++ tailWord_531181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531189 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_531189 : Nat := 118140960795 + 531189 * 2 ^ 59
def prefixEnd_531189 : Nat := 4983230072969 + 3 ^ 40 * 531189 * 2
def baseEnd_531189 : Nat := 272755275381227454294613

theorem tailTrace_531189 : CollatzResearch.WordTrace tailWord_531189 prefixEnd_531189 272755275381227454294613 := by
  unfold tailWord_531189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19374054472600447703732621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12916036315066965135821747 19374054472600447703732621)
  ·
    refine ⟨7265270427225167888899733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19374054472600447703732621 7265270427225167888899733)
    ·
      refine ⟨340559551276179744792175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7265270427225167888899733 340559551276179744792175)
      ·
        refine ⟨510839326914269617188263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340559551276179744792175 510839326914269617188263)
        ·
          refine ⟨766258990371404425782395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510839326914269617188263 766258990371404425782395)
          ·
            refine ⟨1149388485557106638673593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766258990371404425782395 1149388485557106638673593)
            ·
              refine ⟨862041364167829979005195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149388485557106638673593 862041364167829979005195)
              ·
                refine ⟨1293062046251744968507793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862041364167829979005195 1293062046251744968507793)
                ·
                  refine ⟨969796534688808726380845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293062046251744968507793 969796534688808726380845)
                  ·
                    refine ⟨363673700508303272392817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969796534688808726380845 363673700508303272392817)
                    ·
                      refine ⟨272755275381227454294613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363673700508303272392817 272755275381227454294613)
                      ·
                        rfl

theorem cell23_531189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_531189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531189 prefixEnd_531189 := by exact prefixLift 531189
  have htrace : WordTrace (prefixWord ++ tailWord_531189) baseStart_531189 baseEnd_531189 := by
    simpa [prefixWord, tailWord_531189, baseEnd_531189] using wordTrace_append hprefix tailTrace_531189
  have hstable : (prefixWord ++ tailWord_531189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531189).length < 2 ^ (prefixWord ++ tailWord_531189).sum := by decide
  have hdescent : baseEnd_531189 < baseStart_531189 := by decide
  rcases family_descends (prefixWord ++ tailWord_531189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531198 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_531198 : Nat := 118140960795 + 531198 * 2 ^ 59
def prefixEnd_531198 : Nat := 4983230072969 + 3 ^ 40 * 531198 * 2
def baseEnd_531198 : Nat := 272759896707117919082071

theorem tailTrace_531198 : CollatzResearch.WordTrace tailWord_531198 prefixEnd_531198 272759896707117919082071 := by
  unfold tailWord_531198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421797841195980280101281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12916255153045228160540165 2421797841195980280101281)
  ·
    refine ⟨1816348380896985210075961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2421797841195980280101281 1816348380896985210075961)
    ·
      refine ⟨1362261285672738907556971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1816348380896985210075961 1362261285672738907556971)
      ·
        refine ⟨2043391928509108361335457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362261285672738907556971 2043391928509108361335457)
        ·
          refine ⟨1532543946381831271001593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2043391928509108361335457 1532543946381831271001593)
          ·
            refine ⟨1149407959786373453251195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532543946381831271001593 1149407959786373453251195)
            ·
              refine ⟨1724111939679560179876793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149407959786373453251195 1724111939679560179876793)
              ·
                refine ⟨1293083954759670134907595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724111939679560179876793 1293083954759670134907595)
                ·
                  refine ⟨1939625932139505202361393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293083954759670134907595 1939625932139505202361393)
                  ·
                    refine ⟨1454719449104628901771045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939625932139505202361393 1454719449104628901771045)
                    ·
                      refine ⟨272759896707117919082071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1454719449104628901771045 272759896707117919082071)
                      ·
                        rfl

theorem cell23_531198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_531198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531198 prefixEnd_531198 := by exact prefixLift 531198
  have htrace : WordTrace (prefixWord ++ tailWord_531198) baseStart_531198 baseEnd_531198 := by
    simpa [prefixWord, tailWord_531198, baseEnd_531198] using wordTrace_append hprefix tailTrace_531198
  have hstable : (prefixWord ++ tailWord_531198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531198).length < 2 ^ (prefixWord ++ tailWord_531198).sum := by decide
  have hdescent : baseEnd_531198 < baseStart_531198 := by decide
  rcases family_descends (prefixWord ++ tailWord_531198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531228 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_531228 : Nat := 118140960795 + 531228 * 2 ^ 59
def prefixEnd_531228 : Nat := 4983230072969 + 3 ^ 40 * 531228 * 2
def baseEnd_531228 : Nat := 272775301126752801706933

theorem tailTrace_531228 : CollatzResearch.WordTrace tailWord_531228 prefixEnd_531228 272775301126752801706933 := by
  unfold tailWord_531228
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687738459729578682201169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12916984612972771576268225 9687738459729578682201169)
  ·
    refine ⟨7265803844797184011650877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9687738459729578682201169 7265803844797184011650877)
    ·
      refine ⟨2724676441798944004369079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7265803844797184011650877 2724676441798944004369079)
      ·
        refine ⟨4087014662698416006553619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724676441798944004369079 4087014662698416006553619)
        ·
          refine ⟨6130521994047624009830429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087014662698416006553619 6130521994047624009830429)
          ·
            refine ⟨2298945747767859003686411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6130521994047624009830429 2298945747767859003686411)
            ·
              refine ⟨3448418621651788505529617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298945747767859003686411 3448418621651788505529617)
              ·
                refine ⟨2586313966238841379147213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448418621651788505529617 2586313966238841379147213)
                ·
                  refine ⟨969867737339565517180205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2586313966238841379147213 969867737339565517180205)
                  ·
                    refine ⟨363700401502337068942577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969867737339565517180205 363700401502337068942577)
                    ·
                      refine ⟨272775301126752801706933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363700401502337068942577 272775301126752801706933)
                      ·
                        rfl

theorem cell23_531228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_531228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531228 prefixEnd_531228 := by exact prefixLift 531228
  have htrace : WordTrace (prefixWord ++ tailWord_531228) baseStart_531228 baseEnd_531228 := by
    simpa [prefixWord, tailWord_531228, baseEnd_531228] using wordTrace_append hprefix tailTrace_531228
  have hstable : (prefixWord ++ tailWord_531228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531228).length < 2 ^ (prefixWord ++ tailWord_531228).sum := by decide
  have hdescent : baseEnd_531228 < baseStart_531228 := by decide
  rcases family_descends (prefixWord ++ tailWord_531228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531241 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 4, 2]
def baseStart_531241 : Nat := 118140960795 + 531241 * 2 ^ 59
def prefixEnd_531241 : Nat := 4983230072969 + 3 ^ 40 * 531241 * 2
def baseEnd_531241 : Nat := 272781976375261250844373

theorem tailTrace_531241 : CollatzResearch.WordTrace tailWord_531241 prefixEnd_531241 272781976375261250844373 := by
  unfold tailWord_531241
  simp only [CollatzResearch.WordTrace]
  refine ⟨19375951068412060584625577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12917300712274707056417051 19375951068412060584625577)
  ·
    refine ⟨14531963301309045438469183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19375951068412060584625577 14531963301309045438469183)
    ·
      refine ⟨21797944951963568157703775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14531963301309045438469183 21797944951963568157703775)
      ·
        refine ⟨32696917427945352236555663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21797944951963568157703775 32696917427945352236555663)
        ·
          refine ⟨49045376141918028354833495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32696917427945352236555663 49045376141918028354833495)
          ·
            refine ⟨73568064212877042532250243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49045376141918028354833495 73568064212877042532250243)
            ·
              refine ⟨110352096319315563798375365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73568064212877042532250243 110352096319315563798375365)
              ·
                refine ⟨20691018059871668212195381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110352096319315563798375365 20691018059871668212195381)
                ·
                  refine ⟨1939782943112968894893317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20691018059871668212195381 1939782943112968894893317)
                  ·
                    refine ⟨363709301833681667792497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939782943112968894893317 363709301833681667792497)
                    ·
                      refine ⟨272781976375261250844373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363709301833681667792497 272781976375261250844373)
                      ·
                        rfl

theorem cell23_531241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4, 2].length) (baseStart_531241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531241 prefixEnd_531241 := by exact prefixLift 531241
  have htrace : WordTrace (prefixWord ++ tailWord_531241) baseStart_531241 baseEnd_531241 := by
    simpa [prefixWord, tailWord_531241, baseEnd_531241] using wordTrace_append hprefix tailTrace_531241
  have hstable : (prefixWord ++ tailWord_531241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531241).length < 2 ^ (prefixWord ++ tailWord_531241).sum := by decide
  have hdescent : baseEnd_531241 < baseStart_531241 := by decide
  rcases family_descends (prefixWord ++ tailWord_531241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531262 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_531262 : Nat := 118140960795 + 531262 * 2 ^ 59
def prefixEnd_531262 : Nat := 4983230072969 + 3 ^ 40 * 531262 * 2
def baseEnd_531262 : Nat := 272792759469005668681777

theorem tailTrace_531262 : CollatzResearch.WordTrace tailWord_531262 prefixEnd_531262 272792759469005668681777 := by
  unfold tailWord_531262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422089625166997646392505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12917811334223987447426693 2422089625166997646392505)
  ·
    refine ⟨1816567218875248234794379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2422089625166997646392505 1816567218875248234794379)
    ·
      refine ⟨2724850828312872352191569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816567218875248234794379 2724850828312872352191569)
      ·
        refine ⟨2043638121234654264143677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2724850828312872352191569 2043638121234654264143677)
        ·
          refine ⟨766364295462995349053879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2043638121234654264143677 766364295462995349053879)
          ·
            refine ⟨1149546443194493023580819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766364295462995349053879 1149546443194493023580819)
            ·
              refine ⟨1724319664791739535371229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149546443194493023580819 1724319664791739535371229)
              ·
                refine ⟨646619874296902325764211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1724319664791739535371229 646619874296902325764211)
                ·
                  refine ⟨969929811445353488646317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646619874296902325764211 969929811445353488646317)
                  ·
                    refine ⟨363723679292007558242369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 969929811445353488646317 363723679292007558242369)
                    ·
                      refine ⟨272792759469005668681777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363723679292007558242369 272792759469005668681777)
                      ·
                        rfl

theorem cell23_531262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_531262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531262 prefixEnd_531262 := by exact prefixLift 531262
  have htrace : WordTrace (prefixWord ++ tailWord_531262) baseStart_531262 baseEnd_531262 := by
    simpa [prefixWord, tailWord_531262, baseEnd_531262] using wordTrace_append hprefix tailTrace_531262
  have hstable : (prefixWord ++ tailWord_531262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531262).length < 2 ^ (prefixWord ++ tailWord_531262).sum := by decide
  have hdescent : baseEnd_531262 < baseStart_531262 := by decide
  rcases family_descends (prefixWord ++ tailWord_531262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531274 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_531274 : Nat := 118140960795 + 531274 * 2 ^ 59
def prefixEnd_531274 : Nat := 4983230072969 + 3 ^ 40 * 531274 * 2
def baseEnd_531274 : Nat := 272798921236859621731721

theorem tailTrace_531274 : CollatzResearch.WordTrace tailWord_531274 prefixEnd_531274 272798921236859621731721 := by
  unfold tailWord_531274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844288669323126805144219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12918103118195004813717917 4844288669323126805144219)
  ·
    refine ⟨7266433003984690207716329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844288669323126805144219 7266433003984690207716329)
    ·
      refine ⟨5449824752988517655787247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7266433003984690207716329 5449824752988517655787247)
      ·
        refine ⟨8174737129482776483680871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449824752988517655787247 8174737129482776483680871)
        ·
          refine ⟨12262105694224164725521307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174737129482776483680871 12262105694224164725521307)
          ·
            refine ⟨18393158541336247088281961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12262105694224164725521307 18393158541336247088281961)
            ·
              refine ⟨13794868906002185316211471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18393158541336247088281961 13794868906002185316211471)
              ·
                refine ⟨20692303359003277974317207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13794868906002185316211471 20692303359003277974317207)
                ·
                  refine ⟨31038455038504916961475811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20692303359003277974317207 31038455038504916961475811)
                  ·
                    refine ⟨46557682557757375442213717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31038455038504916961475811 46557682557757375442213717)
                    ·
                      refine ⟨272798921236859621731721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 46557682557757375442213717 272798921236859621731721)
                      ·
                        rfl

theorem cell23_531274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_531274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531274 prefixEnd_531274 := by exact prefixLift 531274
  have htrace : WordTrace (prefixWord ++ tailWord_531274) baseStart_531274 baseEnd_531274 := by
    simpa [prefixWord, tailWord_531274, baseEnd_531274] using wordTrace_append hprefix tailTrace_531274
  have hstable : (prefixWord ++ tailWord_531274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531274).length < 2 ^ (prefixWord ++ tailWord_531274).sum := by decide
  have hdescent : baseEnd_531274 < baseStart_531274 := by decide
  rcases family_descends (prefixWord ++ tailWord_531274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531292 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_531292 : Nat := 118140960795 + 531292 * 2 ^ 59
def prefixEnd_531292 : Nat := 4983230072969 + 3 ^ 40 * 531292 * 2
def baseEnd_531292 : Nat := 272808163888640551306639

theorem tailTrace_531292 : CollatzResearch.WordTrace tailWord_531292 prefixEnd_531292 272808163888640551306639 := by
  unfold tailWord_531292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688905595613648147366065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12918540794151530863154753 9688905595613648147366065)
  ·
    refine ⟨7266679196710236110524549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9688905595613648147366065 7266679196710236110524549)
    ·
      refine ⟨1362502349383169270723353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7266679196710236110524549 1362502349383169270723353)
      ·
        refine ⟨1021876762037376953042515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1362502349383169270723353 1021876762037376953042515)
        ·
          refine ⟨1532815143056065429563773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021876762037376953042515 1532815143056065429563773)
          ·
            refine ⟨574805678646024536086415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1532815143056065429563773 574805678646024536086415)
            ·
              refine ⟨862208517969036804129623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574805678646024536086415 862208517969036804129623)
              ·
                refine ⟨1293312776953555206194435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862208517969036804129623 1293312776953555206194435)
                ·
                  refine ⟨1939969165430332809291653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293312776953555206194435 1939969165430332809291653)
                  ·
                    refine ⟨363744218518187401742185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939969165430332809291653 363744218518187401742185)
                    ·
                      refine ⟨272808163888640551306639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363744218518187401742185 272808163888640551306639)
                      ·
                        rfl

theorem cell23_531292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_531292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531292 prefixEnd_531292 := by exact prefixLift 531292
  have htrace : WordTrace (prefixWord ++ tailWord_531292) baseStart_531292 baseEnd_531292 := by
    simpa [prefixWord, tailWord_531292, baseEnd_531292] using wordTrace_append hprefix tailTrace_531292
  have hstable : (prefixWord ++ tailWord_531292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531292).length < 2 ^ (prefixWord ++ tailWord_531292).sum := by decide
  have hdescent : baseEnd_531292 < baseStart_531292 := by decide
  rcases family_descends (prefixWord ++ tailWord_531292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531338 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_531338 : Nat := 118140960795 + 531338 * 2 ^ 59
def prefixEnd_531338 : Nat := 4983230072969 + 3 ^ 40 * 531338 * 2
def baseEnd_531338 : Nat := 272831783998747371331427

theorem tailTrace_531338 : CollatzResearch.WordTrace tailWord_531338 prefixEnd_531338 272831783998747371331427 := by
  unfold tailWord_531338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844872237265161537726667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12919659299373764100604445 4844872237265161537726667)
  ·
    refine ⟨7267308355897742306590001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844872237265161537726667 7267308355897742306590001)
    ·
      refine ⟨5450481266923306729942501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7267308355897742306590001 5450481266923306729942501)
      ·
        refine ⟨1021965237548120011864219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5450481266923306729942501 1021965237548120011864219)
        ·
          refine ⟨1532947856322180017796329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021965237548120011864219 1532947856322180017796329)
          ·
            refine ⟨1149710892241635013347247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532947856322180017796329 1149710892241635013347247)
            ·
              refine ⟨1724566338362452520020871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149710892241635013347247 1724566338362452520020871)
              ·
                refine ⟨2586849507543678780031307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724566338362452520020871 2586849507543678780031307)
                ·
                  refine ⟨3880274261315518170046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586849507543678780031307 3880274261315518170046961)
                  ·
                    refine ⟨2910205695986638627535221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880274261315518170046961 2910205695986638627535221)
                    ·
                      refine ⟨272831783998747371331427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2910205695986638627535221 272831783998747371331427)
                      ·
                        rfl

theorem cell23_531338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_531338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531338 prefixEnd_531338 := by exact prefixLift 531338
  have htrace : WordTrace (prefixWord ++ tailWord_531338) baseStart_531338 baseEnd_531338 := by
    simpa [prefixWord, tailWord_531338, baseEnd_531338] using wordTrace_append hprefix tailTrace_531338
  have hstable : (prefixWord ++ tailWord_531338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531338).length < 2 ^ (prefixWord ++ tailWord_531338).sum := by decide
  have hdescent : baseEnd_531338 < baseStart_531338 := by decide
  rcases family_descends (prefixWord ++ tailWord_531338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531348 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_531348 : Nat := 118140960795 + 531348 * 2 ^ 59
def prefixEnd_531348 : Nat := 4983230072969 + 3 ^ 40 * 531348 * 2
def baseEnd_531348 : Nat := 272836918805292332206381

theorem tailTrace_531348 : CollatzResearch.WordTrace tailWord_531348 prefixEnd_531348 272836918805292332206381 := by
  unfold tailWord_531348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689926839512208929385349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12919902452682945239180465 9689926839512208929385349)
  ·
    refine ⟨1816861282408539174259753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9689926839512208929385349 1816861282408539174259753)
    ·
      refine ⟨1362645961806404380694815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1816861282408539174259753 1362645961806404380694815)
      ·
        refine ⟨2043968942709606571042223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362645961806404380694815 2043968942709606571042223)
        ·
          refine ⟨3065953414064409856563335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2043968942709606571042223 3065953414064409856563335)
          ·
            refine ⟨4598930121096614784845003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065953414064409856563335 4598930121096614784845003)
            ·
              refine ⟨6898395181644922177267505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598930121096614784845003 6898395181644922177267505)
              ·
                refine ⟨5173796386233691632950629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6898395181644922177267505 5173796386233691632950629)
                ·
                  refine ⟨970086822418817181178243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5173796386233691632950629 970086822418817181178243)
                  ·
                    refine ⟨1455130233628225771767365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970086822418817181178243 1455130233628225771767365)
                    ·
                      refine ⟨272836918805292332206381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1455130233628225771767365 272836918805292332206381)
                      ·
                        rfl

theorem cell23_531348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_531348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531348 prefixEnd_531348 := by exact prefixLift 531348
  have htrace : WordTrace (prefixWord ++ tailWord_531348) baseStart_531348 baseEnd_531348 := by
    simpa [prefixWord, tailWord_531348, baseEnd_531348] using wordTrace_append hprefix tailTrace_531348
  have hstable : (prefixWord ++ tailWord_531348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531348).length < 2 ^ (prefixWord ++ tailWord_531348).sum := by decide
  have hdescent : baseEnd_531348 < baseStart_531348 := by decide
  rcases family_descends (prefixWord ++ tailWord_531348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531392 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 1, 4]
def baseStart_531392 : Nat := 118140960795 + 531392 * 2 ^ 59
def prefixEnd_531392 : Nat := 4983230072969 + 3 ^ 40 * 531392 * 2
def baseEnd_531392 : Nat := 90953170651363386685393

theorem tailTrace_531392 : CollatzResearch.WordTrace tailWord_531392 prefixEnd_531392 90953170651363386685393 := by
  unfold tailWord_531392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690729245432506686686215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12920972327243342248914953 9690729245432506686686215)
  ·
    refine ⟨14536093868148760030029323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9690729245432506686686215 14536093868148760030029323)
    ·
      refine ⟨21804140802223140045043985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14536093868148760030029323 21804140802223140045043985)
      ·
        refine ⟨16353105601667355033782989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21804140802223140045043985 16353105601667355033782989)
        ·
          refine ⟨6132414600625258137668621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16353105601667355033782989 6132414600625258137668621)
          ·
            refine ⟨2299655475234471801625733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6132414600625258137668621 2299655475234471801625733)
            ·
              refine ⟨431185401606463462804825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2299655475234471801625733 431185401606463462804825)
              ·
                refine ⟨323389051204847597103619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431185401606463462804825 323389051204847597103619)
                ·
                  refine ⟨485083576807271395655429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323389051204847597103619 485083576807271395655429)
                  ·
                    refine ⟨90953170651363386685393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485083576807271395655429 90953170651363386685393)
                    ·
                      rfl

theorem cell23_531392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_531392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531392 prefixEnd_531392 := by exact prefixLift 531392
  have htrace : WordTrace (prefixWord ++ tailWord_531392) baseStart_531392 baseEnd_531392 := by
    simpa [prefixWord, tailWord_531392, baseEnd_531392] using wordTrace_append hprefix tailTrace_531392
  have hstable : (prefixWord ++ tailWord_531392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531392).length < 2 ^ (prefixWord ++ tailWord_531392).sum := by decide
  have hdescent : baseEnd_531392 < baseStart_531392 := by decide
  rcases family_descends (prefixWord ++ tailWord_531392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531408 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2]
def baseStart_531408 : Nat := 118140960795 + 531408 * 2 ^ 59
def prefixEnd_531408 : Nat := 4983230072969 + 3 ^ 40 * 531408 * 2
def baseEnd_531408 : Nat := 272867727644562097456105

theorem tailTrace_531408 : CollatzResearch.WordTrace tailWord_531408 prefixEnd_531408 272867727644562097456105 := by
  unfold tailWord_531408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691021029403524052977439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12921361372538032070636585 9691021029403524052977439)
  ·
    refine ⟨14536531544105286079466159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691021029403524052977439 14536531544105286079466159)
    ·
      refine ⟨21804797316157929119199239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14536531544105286079466159 21804797316157929119199239)
      ·
        refine ⟨32707195974236893678798859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21804797316157929119199239 32707195974236893678798859)
        ·
          refine ⟨49060793961355340518198289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32707195974236893678798859 49060793961355340518198289)
          ·
            refine ⟨36795595471016505388648717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49060793961355340518198289 36795595471016505388648717)
            ·
              refine ⟨13798348301631189520743269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36795595471016505388648717 13798348301631189520743269)
              ·
                refine ⟨2587190306555848035139363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13798348301631189520743269 2587190306555848035139363)
                ·
                  refine ⟨3880785459833772052709045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587190306555848035139363 3880785459833772052709045)
                  ·
                    refine ⟨363823636859416129941473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3880785459833772052709045 363823636859416129941473)
                    ·
                      refine ⟨272867727644562097456105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363823636859416129941473 272867727644562097456105)
                      ·
                        rfl

theorem cell23_531408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2].length) (baseStart_531408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531408 prefixEnd_531408 := by exact prefixLift 531408
  have htrace : WordTrace (prefixWord ++ tailWord_531408) baseStart_531408 baseEnd_531408 := by
    simpa [prefixWord, tailWord_531408, baseEnd_531408] using wordTrace_append hprefix tailTrace_531408
  have hstable : (prefixWord ++ tailWord_531408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531408).length < 2 ^ (prefixWord ++ tailWord_531408).sum := by decide
  have hdescent : baseEnd_531408 < baseStart_531408 := by decide
  rcases family_descends (prefixWord ++ tailWord_531408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531418 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_531418 : Nat := 118140960795 + 531418 * 2 ^ 59
def prefixEnd_531418 : Nat := 4983230072969 + 3 ^ 40 * 531418 * 2
def baseEnd_531418 : Nat := 90957620817035686110353

theorem tailTrace_531418 : CollatzResearch.WordTrace tailWord_531418 prefixEnd_531418 90957620817035686110353 := by
  unfold tailWord_531418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845601697192704953454727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12921604525847213209212605 4845601697192704953454727)
  ·
    refine ⟨7268402545789057430182091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4845601697192704953454727 7268402545789057430182091)
    ·
      refine ⟨10902603818683586145273137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268402545789057430182091 10902603818683586145273137)
      ·
        refine ⟨8176952864012689608954853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10902603818683586145273137 8176952864012689608954853)
        ·
          refine ⟨1533178662002379301679035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8176952864012689608954853 1533178662002379301679035)
          ·
            refine ⟨2299767993003568952518553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533178662002379301679035 2299767993003568952518553)
            ·
              refine ⟨1724825994752676714388915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299767993003568952518553 1724825994752676714388915)
              ·
                refine ⟨2587238992129015071583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724825994752676714388915 2587238992129015071583373)
                ·
                  refine ⟨970214622048380651843765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2587238992129015071583373 970214622048380651843765)
                  ·
                    refine ⟨90957620817035686110353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 970214622048380651843765 90957620817035686110353)
                    ·
                      rfl

theorem cell23_531418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_531418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531418 prefixEnd_531418 := by exact prefixLift 531418
  have htrace : WordTrace (prefixWord ++ tailWord_531418) baseStart_531418 baseEnd_531418 := by
    simpa [prefixWord, tailWord_531418, baseEnd_531418] using wordTrace_append hprefix tailTrace_531418
  have hstable : (prefixWord ++ tailWord_531418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531418).length < 2 ^ (prefixWord ++ tailWord_531418).sum := by decide
  have hdescent : baseEnd_531418 < baseStart_531418 := by decide
  rcases family_descends (prefixWord ++ tailWord_531418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531432 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_531432 : Nat := 118140960795 + 531432 * 2 ^ 59
def prefixEnd_531432 : Nat := 4983230072969 + 3 ^ 40 * 531432 * 2
def baseEnd_531432 : Nat := 272880051180270003555995

theorem tailTrace_531432 : CollatzResearch.WordTrace tailWord_531432 prefixEnd_531432 272880051180270003555995 := by
  unfold tailWord_531432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691458705360050102414275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12921944940480066803219033 9691458705360050102414275)
  ·
    refine ⟨14537188058040075153621413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691458705360050102414275 14537188058040075153621413)
    ·
      refine ⟨2725722760882514091304015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14537188058040075153621413 2725722760882514091304015)
      ·
        refine ⟨4088584141323771136956023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2725722760882514091304015 4088584141323771136956023)
        ·
          refine ⟨6132876211985656705434035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088584141323771136956023 6132876211985656705434035)
          ·
            refine ⟨9199314317978485058151053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6132876211985656705434035 9199314317978485058151053)
            ·
              refine ⟨3449742869241931896806645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9199314317978485058151053 3449742869241931896806645)
              ·
                refine ⟨323413393991431115325623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3449742869241931896806645 323413393991431115325623)
                ·
                  refine ⟨485120090987146672988435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323413393991431115325623 485120090987146672988435)
                  ·
                    refine ⟨727680136480720009482653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485120090987146672988435 727680136480720009482653)
                    ·
                      refine ⟨272880051180270003555995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727680136480720009482653 272880051180270003555995)
                      ·
                        rfl

theorem cell23_531432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_531432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531432 prefixEnd_531432 := by exact prefixLift 531432
  have htrace : WordTrace (prefixWord ++ tailWord_531432) baseStart_531432 baseEnd_531432 := by
    simpa [prefixWord, tailWord_531432, baseEnd_531432] using wordTrace_append hprefix tailTrace_531432
  have hstable : (prefixWord ++ tailWord_531432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531432).length < 2 ^ (prefixWord ++ tailWord_531432).sum := by decide
  have hdescent : baseEnd_531432 < baseStart_531432 := by decide
  rcases family_descends (prefixWord ++ tailWord_531432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531451 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_531451 : Nat := 118140960795 + 531451 * 2 ^ 59
def prefixEnd_531451 : Nat := 4983230072969 + 3 ^ 40 * 531451 * 2
def baseEnd_531451 : Nat := 272889807312705429218407

theorem tailTrace_531451 : CollatzResearch.WordTrace tailWord_531451 prefixEnd_531451 272889807312705429218407 := by
  unfold tailWord_531451
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383610397651266449770207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12922406931767510966513471 19383610397651266449770207)
  ·
    refine ⟨29075415596476899674655311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19383610397651266449770207 29075415596476899674655311)
    ·
      refine ⟨43613123394715349511982967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29075415596476899674655311 43613123394715349511982967)
      ·
        refine ⟨65419685092073024267974451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43613123394715349511982967 65419685092073024267974451)
        ·
          refine ⟨98129527638109536401961677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65419685092073024267974451 98129527638109536401961677)
          ·
            refine ⟨36798572864291076150735629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98129527638109536401961677 36798572864291076150735629)
            ·
              refine ⟨13799464824109153556525861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36798572864291076150735629 13799464824109153556525861)
              ·
                refine ⟨2587399654520466291848599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13799464824109153556525861 2587399654520466291848599)
                ·
                  refine ⟨3881099481780699437772899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587399654520466291848599 3881099481780699437772899)
                  ·
                    refine ⟨5821649222671049156659349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881099481780699437772899 5821649222671049156659349)
                    ·
                      refine ⟨272889807312705429218407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5821649222671049156659349 272889807312705429218407)
                      ·
                        rfl

theorem cell23_531451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_531451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531451 prefixEnd_531451 := by exact prefixLift 531451
  have htrace : WordTrace (prefixWord ++ tailWord_531451) baseStart_531451 baseEnd_531451 := by
    simpa [prefixWord, tailWord_531451, baseEnd_531451] using wordTrace_append hprefix tailTrace_531451
  have hstable : (prefixWord ++ tailWord_531451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531451).length < 2 ^ (prefixWord ++ tailWord_531451).sum := by decide
  have hdescent : baseEnd_531451 < baseStart_531451 := by decide
  rcases family_descends (prefixWord ++ tailWord_531451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531461 : List Nat := [1, 3, 1, 1, 2, 3, 2, 10]
def baseStart_531461 : Nat := 118140960795 + 531461 * 2 ^ 59
def prefixEnd_531461 : Nat := 4983230072969 + 3 ^ 40 * 531461 * 2
def baseEnd_531461 : Nat := 10107220078490755188643

theorem tailTrace_531461 : CollatzResearch.WordTrace tailWord_531461 prefixEnd_531461 10107220078490755188643 := by
  unfold tailWord_531461
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383975127615038157634237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12922650085076692105089491 19383975127615038157634237)
  ·
    refine ⟨7268990672855639309112839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19383975127615038157634237 7268990672855639309112839)
    ·
      refine ⟨10903486009283458963669259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268990672855639309112839 10903486009283458963669259)
      ·
        refine ⟨16355229013925188445503889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10903486009283458963669259 16355229013925188445503889)
        ·
          refine ⟨12266421760443891334127917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16355229013925188445503889 12266421760443891334127917)
          ·
            refine ⟨4599908160166459250297969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12266421760443891334127917 4599908160166459250297969)
            ·
              refine ⟨3449931120124844437723477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599908160166459250297969 3449931120124844437723477)
              ·
                refine ⟨10107220078490755188643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3449931120124844437723477 10107220078490755188643)
                ·
                  rfl

theorem cell23_531461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 10].length) (baseStart_531461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531461 prefixEnd_531461 := by exact prefixLift 531461
  have htrace : WordTrace (prefixWord ++ tailWord_531461) baseStart_531461 baseEnd_531461 := by
    simpa [prefixWord, tailWord_531461, baseEnd_531461] using wordTrace_append hprefix tailTrace_531461
  have hstable : (prefixWord ++ tailWord_531461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531461).length < 2 ^ (prefixWord ++ tailWord_531461).sum := by decide
  have hdescent : baseEnd_531461 < baseStart_531461 := by decide
  rcases family_descends (prefixWord ++ tailWord_531461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531468 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_531468 : Nat := 118140960795 + 531468 * 2 ^ 59
def prefixEnd_531468 : Nat := 4983230072969 + 3 ^ 40 * 531468 * 2
def baseEnd_531468 : Nat := 272898536483831862705829

theorem tailTrace_531468 : CollatzResearch.WordTrace tailWord_531468 prefixEnd_531468 272898536483831862705829 := by
  unfold tailWord_531468
  simp only [CollatzResearch.WordTrace]
  refine ⟨9692115219294839176569529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12922820292393118902092705 9692115219294839176569529)
  ·
    refine ⟨7269086414471129382427147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9692115219294839176569529 7269086414471129382427147)
    ·
      refine ⟨10903629621706694073640721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7269086414471129382427147 10903629621706694073640721)
      ·
        refine ⟨8177722216280020555230541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10903629621706694073640721 8177722216280020555230541)
        ·
          refine ⟨3066645831105007708211453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8177722216280020555230541 3066645831105007708211453)
          ·
            refine ⟨1149992186664377890579295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3066645831105007708211453 1149992186664377890579295)
            ·
              refine ⟨1724988279996566835868943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149992186664377890579295 1724988279996566835868943)
              ·
                refine ⟨2587482419994850253803415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724988279996566835868943 2587482419994850253803415)
                ·
                  refine ⟨3881223629992275380705123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587482419994850253803415 3881223629992275380705123)
                  ·
                    refine ⟨5821835444988413071057685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881223629992275380705123 5821835444988413071057685)
                    ·
                      refine ⟨272898536483831862705829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5821835444988413071057685 272898536483831862705829)
                      ·
                        rfl

theorem cell23_531468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_531468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531468 prefixEnd_531468 := by exact prefixLift 531468
  have htrace : WordTrace (prefixWord ++ tailWord_531468) baseStart_531468 baseEnd_531468 := by
    simpa [prefixWord, tailWord_531468, baseEnd_531468] using wordTrace_append hprefix tailTrace_531468
  have hstable : (prefixWord ++ tailWord_531468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531468).length < 2 ^ (prefixWord ++ tailWord_531468).sum := by decide
  have hdescent : baseEnd_531468 < baseStart_531468 := by decide
  rcases family_descends (prefixWord ++ tailWord_531468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531492 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_531492 : Nat := 118140960795 + 531492 * 2 ^ 59
def prefixEnd_531492 : Nat := 4983230072969 + 3 ^ 40 * 531492 * 2
def baseEnd_531492 : Nat := 272910860019539768805719

theorem tailTrace_531492 : CollatzResearch.WordTrace tailWord_531492 prefixEnd_531492 272910860019539768805719 := by
  unfold tailWord_531492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9692552895251365226006365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12923403860335153634675153 9692552895251365226006365)
  ·
    refine ⟨3634707335719261959752387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9692552895251365226006365 3634707335719261959752387)
    ·
      refine ⟨5452061003578892939628581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634707335719261959752387 5452061003578892939628581)
      ·
        refine ⟨1022261438171042426180359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5452061003578892939628581 1022261438171042426180359)
        ·
          refine ⟨1533392157256563639270539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022261438171042426180359 1533392157256563639270539)
          ·
            refine ⟨2300088235884845458905809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533392157256563639270539 2300088235884845458905809)
            ·
              refine ⟨1725066176913634094179357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300088235884845458905809 1725066176913634094179357)
              ·
                refine ⟨646899816342612785317259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1725066176913634094179357 646899816342612785317259)
                ·
                  refine ⟨970349724513919177975889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646899816342612785317259 970349724513919177975889)
                  ·
                    refine ⟨727762293385439383481917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970349724513919177975889 727762293385439383481917)
                    ·
                      refine ⟨272910860019539768805719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727762293385439383481917 272910860019539768805719)
                      ·
                        rfl

theorem cell23_531492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_531492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531492 prefixEnd_531492 := by exact prefixLift 531492
  have htrace : WordTrace (prefixWord ++ tailWord_531492) baseStart_531492 baseEnd_531492 := by
    simpa [prefixWord, tailWord_531492, baseEnd_531492] using wordTrace_append hprefix tailTrace_531492
  have hstable : (prefixWord ++ tailWord_531492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531492).length < 2 ^ (prefixWord ++ tailWord_531492).sum := by decide
  have hdescent : baseEnd_531492 < baseStart_531492 := by decide
  rcases family_descends (prefixWord ++ tailWord_531492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531495 : List Nat := [1, 1, 7, 1, 1, 3, 9]
def baseStart_531495 : Nat := 118140960795 + 531495 * 2 ^ 59
def prefixEnd_531495 : Nat := 4983230072969 + 3 ^ 40 * 531495 * 2
def baseEnd_531495 : Nat := 3369288894586459963805

theorem tailTrace_531495 : CollatzResearch.WordTrace tailWord_531495 prefixEnd_531495 3369288894586459963805 := by
  unfold tailWord_531495
  simp only [CollatzResearch.WordTrace]
  refine ⟨19385215209491861964371939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12923476806327907976247959 19385215209491861964371939)
  ·
    refine ⟨29077822814237792946557909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19385215209491861964371939 29077822814237792946557909)
    ·
      refine ⟨681511472208698272184951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 29077822814237792946557909 681511472208698272184951)
      ·
        refine ⟨1022267208313047408277427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681511472208698272184951 1022267208313047408277427)
        ·
          refine ⟨1533400812469571112416141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022267208313047408277427 1533400812469571112416141)
          ·
            refine ⟨575025304676089167156053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1533400812469571112416141 575025304676089167156053)
            ·
              refine ⟨3369288894586459963805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 575025304676089167156053 3369288894586459963805)
              ·
                rfl

theorem cell23_531495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 9].length) (baseStart_531495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531495 prefixEnd_531495 := by exact prefixLift 531495
  have htrace : WordTrace (prefixWord ++ tailWord_531495) baseStart_531495 baseEnd_531495 := by
    simpa [prefixWord, tailWord_531495, baseEnd_531495] using wordTrace_append hprefix tailTrace_531495
  have hstable : (prefixWord ++ tailWord_531495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531495).length < 2 ^ (prefixWord ++ tailWord_531495).sum := by decide
  have hdescent : baseEnd_531495 < baseStart_531495 := by decide
  rcases family_descends (prefixWord ++ tailWord_531495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531505 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_531505 : Nat := 118140960795 + 531505 * 2 ^ 59
def prefixEnd_531505 : Nat := 4983230072969 + 3 ^ 40 * 531505 * 2
def baseEnd_531505 : Nat := 272917535268048217943159

theorem tailTrace_531505 : CollatzResearch.WordTrace tailWord_531505 prefixEnd_531505 272917535268048217943159 := by
  unfold tailWord_531505
  simp only [CollatzResearch.WordTrace]
  refine ⟨19385579939455633672235969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12923719959637089114823979 19385579939455633672235969)
  ·
    refine ⟨14539184954591725254176977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19385579939455633672235969 14539184954591725254176977)
    ·
      refine ⟨10904388715943793940632733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14539184954591725254176977 10904388715943793940632733)
      ·
        refine ⟨4089145768478922727737275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10904388715943793940632733 4089145768478922727737275)
        ·
          refine ⟨6133718652718384091605913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089145768478922727737275 6133718652718384091605913)
          ·
            refine ⟨4600288989538788068704435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6133718652718384091605913 4600288989538788068704435)
            ·
              refine ⟨6900433484308182103056653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600288989538788068704435 6900433484308182103056653)
              ·
                refine ⟨2587662556615568288646245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6900433484308182103056653 2587662556615568288646245)
                ·
                  refine ⟨485186729365419054121171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2587662556615568288646245 485186729365419054121171)
                  ·
                    refine ⟨727780094048128581181757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485186729365419054121171 727780094048128581181757)
                    ·
                      refine ⟨272917535268048217943159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727780094048128581181757 272917535268048217943159)
                      ·
                        rfl

theorem cell23_531505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_531505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531505 prefixEnd_531505 := by exact prefixLift 531505
  have htrace : WordTrace (prefixWord ++ tailWord_531505) baseStart_531505 baseEnd_531505 := by
    simpa [prefixWord, tailWord_531505, baseEnd_531505] using wordTrace_append hprefix tailTrace_531505
  have hstable : (prefixWord ++ tailWord_531505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531505).length < 2 ^ (prefixWord ++ tailWord_531505).sum := by decide
  have hdescent : baseEnd_531505 < baseStart_531505 := by decide
  rcases family_descends (prefixWord ++ tailWord_531505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531506 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_531506 : Nat := 118140960795 + 531506 * 2 ^ 59
def prefixEnd_531506 : Nat := 4983230072969 + 3 ^ 40 * 531506 * 2
def baseEnd_531506 : Nat := 272918048748702714030655

theorem tailTrace_531506 : CollatzResearch.WordTrace tailWord_531506 prefixEnd_531506 272918048748702714030655 := by
  unfold tailWord_531506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846404103113002710755593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12923744274968007228681581 4846404103113002710755593)
  ·
    refine ⟨3634803077334752033066695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4846404103113002710755593 3634803077334752033066695)
    ·
      refine ⟨5452204616002128049600043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634803077334752033066695 5452204616002128049600043)
      ·
        refine ⟨8178306924003192074400065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5452204616002128049600043 8178306924003192074400065)
        ·
          refine ⟨6133730193002394055800049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8178306924003192074400065 6133730193002394055800049)
          ·
            refine ⟨4600297644751795541850037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6133730193002394055800049 4600297644751795541850037)
            ·
              refine ⟨431277904195480832048441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4600297644751795541850037 431277904195480832048441)
              ·
                refine ⟨323458428146610624036331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431277904195480832048441 323458428146610624036331)
                ·
                  refine ⟨485187642219915936054497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323458428146610624036331 485187642219915936054497)
                  ·
                    refine ⟨363890731664936952040873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 485187642219915936054497 363890731664936952040873)
                    ·
                      refine ⟨272918048748702714030655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363890731664936952040873 272918048748702714030655)
                      ·
                        rfl

theorem cell23_531506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_531506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531506 prefixEnd_531506 := by exact prefixLift 531506
  have htrace : WordTrace (prefixWord ++ tailWord_531506) baseStart_531506 baseEnd_531506 := by
    simpa [prefixWord, tailWord_531506, baseEnd_531506] using wordTrace_append hprefix tailTrace_531506
  have hstable : (prefixWord ++ tailWord_531506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531506).length < 2 ^ (prefixWord ++ tailWord_531506).sum := by decide
  have hdescent : baseEnd_531506 < baseStart_531506 := by decide
  rcases family_descends (prefixWord ++ tailWord_531506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531526 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_531526 : Nat := 118140960795 + 531526 * 2 ^ 59
def prefixEnd_531526 : Nat := 4983230072969 + 3 ^ 40 * 531526 * 2
def baseEnd_531526 : Nat := 272928318361792635780563

theorem tailTrace_531526 : CollatzResearch.WordTrace tailWord_531526 prefixEnd_531526 272928318361792635780563 := by
  unfold tailWord_531526
  simp only [CollatzResearch.WordTrace]
  refine ⟨605823308511861070585951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12924230581586369505833621 605823308511861070585951)
  ·
    refine ⟨908734962767791605878927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605823308511861070585951 908734962767791605878927)
    ·
      refine ⟨1363102444151687408818391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908734962767791605878927 1363102444151687408818391)
      ·
        refine ⟨2044653666227531113227587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363102444151687408818391 2044653666227531113227587)
        ·
          refine ⟨3066980499341296669841381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044653666227531113227587 3066980499341296669841381)
          ·
            refine ⟨575058843626493125595259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3066980499341296669841381 575058843626493125595259)
            ·
              refine ⟨862588265439739688392889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575058843626493125595259 862588265439739688392889)
              ·
                refine ⟨646941199079804766294667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862588265439739688392889 646941199079804766294667)
                ·
                  refine ⟨970411798619707149442001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646941199079804766294667 970411798619707149442001)
                  ·
                    refine ⟨727808848964780362081501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970411798619707149442001 727808848964780362081501)
                    ·
                      refine ⟨272928318361792635780563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727808848964780362081501 272928318361792635780563)
                      ·
                        rfl

theorem cell23_531526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_531526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531526 prefixEnd_531526 := by exact prefixLift 531526
  have htrace : WordTrace (prefixWord ++ tailWord_531526) baseStart_531526 baseEnd_531526 := by
    simpa [prefixWord, tailWord_531526, baseEnd_531526] using wordTrace_append hprefix tailTrace_531526
  have hstable : (prefixWord ++ tailWord_531526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531526).length < 2 ^ (prefixWord ++ tailWord_531526).sum := by decide
  have hdescent : baseEnd_531526 < baseStart_531526 := by decide
  rcases family_descends (prefixWord ++ tailWord_531526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531565 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_531565 : Nat := 118140960795 + 531565 * 2 ^ 59
def prefixEnd_531565 : Nat := 4983230072969 + 3 ^ 40 * 531565 * 2
def baseEnd_531565 : Nat := 272948344107317983192883

theorem tailTrace_531565 : CollatzResearch.WordTrace tailWord_531565 prefixEnd_531565 272948344107317983192883 := by
  unfold tailWord_531565
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387768319238263919420149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925178879492175946280099 19387768319238263919420149)
  ·
    refine ⟨1817603279928587242445639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19387768319238263919420149 1817603279928587242445639)
    ·
      refine ⟨2726404919892880863668459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817603279928587242445639 2726404919892880863668459)
      ·
        refine ⟨4089607379839321295502689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726404919892880863668459 4089607379839321295502689)
        ·
          refine ⟨3067205534879490971627017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089607379839321295502689 3067205534879490971627017)
          ·
            refine ⟨2300404151159618228720263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067205534879490971627017 2300404151159618228720263)
            ·
              refine ⟨3450606226739427343080395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300404151159618228720263 3450606226739427343080395)
              ·
                refine ⟨5175909340109141014620593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450606226739427343080395 5175909340109141014620593)
                ·
                  refine ⟨3881932005081855760965445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5175909340109141014620593 3881932005081855760965445)
                  ·
                    refine ⟨727862250952847955181021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3881932005081855760965445 727862250952847955181021)
                    ·
                      refine ⟨272948344107317983192883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727862250952847955181021 272948344107317983192883)
                      ·
                        rfl

theorem cell23_531565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_531565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531565 prefixEnd_531565 := by exact prefixLift 531565
  have htrace : WordTrace (prefixWord ++ tailWord_531565) baseStart_531565 baseEnd_531565 := by
    simpa [prefixWord, tailWord_531565, baseEnd_531565] using wordTrace_append hprefix tailTrace_531565
  have hstable : (prefixWord ++ tailWord_531565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531565).length < 2 ^ (prefixWord ++ tailWord_531565).sum := by decide
  have hdescent : baseEnd_531565 < baseStart_531565 := by decide
  rcases family_descends (prefixWord ++ tailWord_531565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531568 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 7]
def baseStart_531568 : Nat := 118140960795 + 531568 * 2 ^ 59
def prefixEnd_531568 : Nat := 4983230072969 + 3 ^ 40 * 531568 * 2
def baseEnd_531568 : Nat := 30327764949920163495041

theorem tailTrace_531568 : CollatzResearch.WordTrace tailWord_531568 prefixEnd_531568 30327764949920163495041 := by
  unfold tailWord_531568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693938869113697715889679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12925251825484930287852905 9693938869113697715889679)
  ·
    refine ⟨14540908303670546573834519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693938869113697715889679 14540908303670546573834519)
    ·
      refine ⟨21811362455505819860751779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14540908303670546573834519 21811362455505819860751779)
      ·
        refine ⟨32717043683258729791127669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21811362455505819860751779 32717043683258729791127669)
        ·
          refine ⟨3067222845305505917918219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32717043683258729791127669 3067222845305505917918219)
          ·
            refine ⟨4600834267958258876877329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3067222845305505917918219 4600834267958258876877329)
            ·
              refine ⟨3450625700968694157657997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600834267958258876877329 3450625700968694157657997)
              ·
                refine ⟨1293984637863260309121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3450625700968694157657997 1293984637863260309121749)
                ·
                  refine ⟨30327764949920163495041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1293984637863260309121749 30327764949920163495041)
                  ·
                    rfl

theorem cell23_531568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_531568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531568 prefixEnd_531568 := by exact prefixLift 531568
  have htrace : WordTrace (prefixWord ++ tailWord_531568) baseStart_531568 baseEnd_531568 := by
    simpa [prefixWord, tailWord_531568, baseEnd_531568] using wordTrace_append hprefix tailTrace_531568
  have hstable : (prefixWord ++ tailWord_531568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531568).length < 2 ^ (prefixWord ++ tailWord_531568).sum := by decide
  have hdescent : baseEnd_531568 < baseStart_531568 := by decide
  rcases family_descends (prefixWord ++ tailWord_531568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531585 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 7]
def baseStart_531585 : Nat := 118140960795 + 531585 * 2 ^ 59
def prefixEnd_531585 : Nat := 4983230072969 + 3 ^ 40 * 531585 * 2
def baseEnd_531585 : Nat := 30328734857823100549199

theorem tailTrace_531585 : CollatzResearch.WordTrace tailWord_531585 prefixEnd_531585 30328734857823100549199 := by
  unfold tailWord_531585
  simp only [CollatzResearch.WordTrace]
  refine ⟨19388497779165807335148209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12925665186110538223432139 19388497779165807335148209)
  ·
    refine ⟨14541373334374355501361157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19388497779165807335148209 14541373334374355501361157)
    ·
      refine ⟨2726507500195191656505217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14541373334374355501361157 2726507500195191656505217)
      ·
        refine ⟨2044880625146393742378913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2726507500195191656505217 2044880625146393742378913)
        ·
          refine ⟨1533660468859795306784185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044880625146393742378913 1533660468859795306784185)
          ·
            refine ⟨1150245351644846480088139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533660468859795306784185 1150245351644846480088139)
            ·
              refine ⟨1725368027467269720132209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150245351644846480088139 1725368027467269720132209)
              ·
                refine ⟨1294026020600452290099157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725368027467269720132209 1294026020600452290099157)
                ·
                  refine ⟨30328734857823100549199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1294026020600452290099157 30328734857823100549199)
                  ·
                    rfl

theorem cell23_531585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_531585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531585 prefixEnd_531585 := by exact prefixLift 531585
  have htrace : WordTrace (prefixWord ++ tailWord_531585) baseStart_531585 baseEnd_531585 := by
    simpa [prefixWord, tailWord_531585, baseEnd_531585] using wordTrace_append hprefix tailTrace_531585
  have hstable : (prefixWord ++ tailWord_531585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531585).length < 2 ^ (prefixWord ++ tailWord_531585).sum := by decide
  have hdescent : baseEnd_531585 < baseStart_531585 := by decide
  rcases family_descends (prefixWord ++ tailWord_531585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531602 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_531602 : Nat := 118140960795 + 531602 * 2 ^ 59
def prefixEnd_531602 : Nat := 4983230072969 + 3 ^ 40 * 531602 * 2
def baseEnd_531602 : Nat := 30329704765726037603357

theorem tailTrace_531602 : CollatzResearch.WordTrace tailWord_531602 prefixEnd_531602 30329704765726037603357 := by
  unfold tailWord_531602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847279455026054809629265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12926078546736146159011373 4847279455026054809629265)
  ·
    refine ⟨3635459591269541107221949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4847279455026054809629265 3635459591269541107221949)
    ·
      refine ⟨1363297346726077915208231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3635459591269541107221949 1363297346726077915208231)
      ·
        refine ⟨2044946020089116872812347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363297346726077915208231 2044946020089116872812347)
        ·
          refine ⟨3067419030133675309218521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044946020089116872812347 3067419030133675309218521)
          ·
            refine ⟨2300564272600256481913891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067419030133675309218521 2300564272600256481913891)
            ·
              refine ⟨3450846408900384722870837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300564272600256481913891 3450846408900384722870837)
              ·
                refine ⟨323516850834411067769141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3450846408900384722870837 323516850834411067769141)
                ·
                  refine ⟨30329704765726037603357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323516850834411067769141 30329704765726037603357)
                  ·
                    rfl

theorem cell23_531602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_531602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531602 prefixEnd_531602 := by exact prefixLift 531602
  have htrace : WordTrace (prefixWord ++ tailWord_531602) baseStart_531602 baseEnd_531602 := by
    simpa [prefixWord, tailWord_531602, baseEnd_531602] using wordTrace_append hprefix tailTrace_531602
  have hstable : (prefixWord ++ tailWord_531602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531602).length < 2 ^ (prefixWord ++ tailWord_531602).sum := by decide
  have hdescent : baseEnd_531602 < baseStart_531602 := by decide
  rcases family_descends (prefixWord ++ tailWord_531602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531605 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 7, 2]
def baseStart_531605 : Nat := 118140960795 + 531605 * 2 ^ 59
def prefixEnd_531605 : Nat := 4983230072969 + 3 ^ 40 * 531605 * 2
def baseEnd_531605 : Nat := 272968883333497826692699

theorem tailTrace_531605 : CollatzResearch.WordTrace tailWord_531605 prefixEnd_531605 272968883333497826692699 := by
  unfold tailWord_531605
  simp only [CollatzResearch.WordTrace]
  refine ⟨19389227239093350750876269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12926151492728900500584179 19389227239093350750876269)
  ·
    refine ⟨7270960214660006531578601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19389227239093350750876269 7270960214660006531578601)
    ·
      refine ⟨5453220160995004898683951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7270960214660006531578601 5453220160995004898683951)
      ·
        refine ⟨8179830241492507348025927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453220160995004898683951 8179830241492507348025927)
        ·
          refine ⟨12269745362238761022038891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8179830241492507348025927 12269745362238761022038891)
          ·
            refine ⟨18404618043358141533058337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12269745362238761022038891 18404618043358141533058337)
            ·
              refine ⟨13803463532518606149793753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18404618043358141533058337 13803463532518606149793753)
              ·
                refine ⟨10352597649388954612345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13803463532518606149793753 10352597649388954612345315)
                ·
                  refine ⟨15528896474083431918517973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10352597649388954612345315 15528896474083431918517973)
                  ·
                    refine ⟨363958511111330435590265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15528896474083431918517973 363958511111330435590265)
                    ·
                      refine ⟨272968883333497826692699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 363958511111330435590265 272968883333497826692699)
                      ·
                        rfl

theorem cell23_531605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_531605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531605 prefixEnd_531605 := by exact prefixLift 531605
  have htrace : WordTrace (prefixWord ++ tailWord_531605) baseStart_531605 baseEnd_531605 := by
    simpa [prefixWord, tailWord_531605, baseEnd_531605] using wordTrace_append hprefix tailTrace_531605
  have hstable : (prefixWord ++ tailWord_531605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531605).length < 2 ^ (prefixWord ++ tailWord_531605).sum := by decide
  have hdescent : baseEnd_531605 < baseStart_531605 := by decide
  rcases family_descends (prefixWord ++ tailWord_531605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531655 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_531655 : Nat := 118140960795 + 531655 * 2 ^ 59
def prefixEnd_531655 : Nat := 4983230072969 + 3 ^ 40 * 531655 * 2
def baseEnd_531655 : Nat := 272994557366222631067469

theorem tailTrace_531655 : CollatzResearch.WordTrace tailWord_531655 prefixEnd_531655 272994557366222631067469 := by
  unfold tailWord_531655
  simp only [CollatzResearch.WordTrace]
  refine ⟨19391050888912209290196419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12927367259274806193464279 19391050888912209290196419)
  ·
    refine ⟨29086576333368313935294629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19391050888912209290196419 29086576333368313935294629)
    ·
      refine ⟨5453733062506558862867743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29086576333368313935294629 5453733062506558862867743)
      ·
        refine ⟨8180599593759838294301615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453733062506558862867743 8180599593759838294301615)
        ·
          refine ⟨12270899390639757441452423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180599593759838294301615 12270899390639757441452423)
          ·
            refine ⟨18406349085959636162178635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12270899390639757441452423 18406349085959636162178635)
            ·
              refine ⟨27609523628939454243267953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18406349085959636162178635 27609523628939454243267953)
              ·
                refine ⟨20707142721704590682450965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27609523628939454243267953 20707142721704590682450965)
                ·
                  refine ⟨970647315079902688239889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20707142721704590682450965 970647315079902688239889)
                  ·
                    refine ⟨727985486309927016179917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970647315079902688239889 727985486309927016179917)
                    ·
                      refine ⟨272994557366222631067469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 727985486309927016179917 272994557366222631067469)
                      ·
                        rfl

theorem cell23_531655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_531655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531655 prefixEnd_531655 := by exact prefixLift 531655
  have htrace : WordTrace (prefixWord ++ tailWord_531655) baseStart_531655 baseEnd_531655 := by
    simpa [prefixWord, tailWord_531655, baseEnd_531655] using wordTrace_append hprefix tailTrace_531655
  have hstable : (prefixWord ++ tailWord_531655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531655).length < 2 ^ (prefixWord ++ tailWord_531655).sum := by decide
  have hdescent : baseEnd_531655 < baseStart_531655 := by decide
  rcases family_descends (prefixWord ++ tailWord_531655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531692 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 6]
def baseStart_531692 : Nat := 118140960795 + 531692 * 2 ^ 59
def prefixEnd_531692 : Nat := 4983230072969 + 3 ^ 40 * 531692 * 2
def baseEnd_531692 : Nat := 30334839572270998478311

theorem tailTrace_531692 : CollatzResearch.WordTrace tailWord_531692 prefixEnd_531692 30334839572270998478311 := by
  unfold tailWord_531692
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696200194889082304646665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12928266926518776406195553 9696200194889082304646665)
  ·
    refine ⟨7272150146166811728484999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9696200194889082304646665 7272150146166811728484999)
    ·
      refine ⟨10908225219250217592727499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7272150146166811728484999 10908225219250217592727499)
      ·
        refine ⟨16362337828875326389091249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10908225219250217592727499 16362337828875326389091249)
        ·
          refine ⟨12271753371656494791818437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16362337828875326389091249 12271753371656494791818437)
          ·
            refine ⟨2300953757185592773465957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12271753371656494791818437 2300953757185592773465957)
            ·
              refine ⟨431428829472298645024867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2300953757185592773465957 431428829472298645024867)
              ·
                refine ⟨647143244208447967537301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431428829472298645024867 647143244208447967537301)
                ·
                  refine ⟨30334839572270998478311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647143244208447967537301 30334839572270998478311)
                  ·
                    rfl

theorem cell23_531692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_531692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531692 prefixEnd_531692 := by exact prefixLift 531692
  have htrace : WordTrace (prefixWord ++ tailWord_531692) baseStart_531692 baseEnd_531692 := by
    simpa [prefixWord, tailWord_531692, baseEnd_531692] using wordTrace_append hprefix tailTrace_531692
  have hstable : (prefixWord ++ tailWord_531692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531692).length < 2 ^ (prefixWord ++ tailWord_531692).sum := by decide
  have hdescent : baseEnd_531692 < baseStart_531692 := by decide
  rcases family_descends (prefixWord ++ tailWord_531692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531705 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_531705 : Nat := 118140960795 + 531705 * 2 ^ 59
def prefixEnd_531705 : Nat := 4983230072969 + 3 ^ 40 * 531705 * 2
def baseEnd_531705 : Nat := 91006743799649145147413

theorem tailTrace_531705 : CollatzResearch.WordTrace tailWord_531705 prefixEnd_531705 91006743799649145147413 := by
  unfold tailWord_531705
  simp only [CollatzResearch.WordTrace]
  refine ⟨19392874538731067829516569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12928583025820711886344379 19392874538731067829516569)
  ·
    refine ⟨14544655904048300872137427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19392874538731067829516569 14544655904048300872137427)
    ·
      refine ⟨21816983856072451308206141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14544655904048300872137427 21816983856072451308206141)
      ·
        refine ⟨8181368946027169240577303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21816983856072451308206141 8181368946027169240577303)
        ·
          refine ⟨12272053419040753860865955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8181368946027169240577303 12272053419040753860865955)
          ·
            refine ⟨18408080128561130791298933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12272053419040753860865955 18408080128561130791298933)
            ·
              refine ⟨1725757512052606011684275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18408080128561130791298933 1725757512052606011684275)
              ·
                refine ⟨2588636268078909017526413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725757512052606011684275 2588636268078909017526413)
                ·
                  refine ⟨970738600529590881572405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2588636268078909017526413 970738600529590881572405)
                  ·
                    refine ⟨91006743799649145147413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 970738600529590881572405 91006743799649145147413)
                    ·
                      rfl

theorem cell23_531705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_531705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531705 prefixEnd_531705 := by exact prefixLift 531705
  have htrace : WordTrace (prefixWord ++ tailWord_531705) baseStart_531705 baseEnd_531705 := by
    simpa [prefixWord, tailWord_531705, baseEnd_531705] using wordTrace_append hprefix tailTrace_531705
  have hstable : (prefixWord ++ tailWord_531705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531705).length < 2 ^ (prefixWord ++ tailWord_531705).sum := by decide
  have hdescent : baseEnd_531705 < baseStart_531705 := by decide
  rcases family_descends (prefixWord ++ tailWord_531705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531735 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 6]
def baseStart_531735 : Nat := 118140960795 + 531735 * 2 ^ 59
def prefixEnd_531735 : Nat := 4983230072969 + 3 ^ 40 * 531735 * 2
def baseEnd_531735 : Nat := 91011878606194106022367

theorem tailTrace_531735 : CollatzResearch.WordTrace tailWord_531735 prefixEnd_531735 91011878606194106022367 := by
  unfold tailWord_531735
  simp only [CollatzResearch.WordTrace]
  refine ⟨19393968728622382953108659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12929312485748255302072439 19393968728622382953108659)
  ·
    refine ⟨29090953092933574429662989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19393968728622382953108659 29090953092933574429662989)
    ·
      refine ⟨10909107409850090411123621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29090953092933574429662989 10909107409850090411123621)
      ·
        refine ⟨2045457639346891952085679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10909107409850090411123621 2045457639346891952085679)
        ·
          refine ⟨3068186459020337928128519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2045457639346891952085679 3068186459020337928128519)
          ·
            refine ⟨4602279688530506892192779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068186459020337928128519 4602279688530506892192779)
            ·
              refine ⟨6903419532795760338289169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602279688530506892192779 6903419532795760338289169)
              ·
                refine ⟨5177564649596820253716877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6903419532795760338289169 5177564649596820253716877)
                ·
                  refine ⟨1941586743598807595143829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5177564649596820253716877 1941586743598807595143829)
                  ·
                    refine ⟨91011878606194106022367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1941586743598807595143829 91011878606194106022367)
                    ·
                      rfl

theorem cell23_531735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_531735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531735 prefixEnd_531735 := by exact prefixLift 531735
  have htrace : WordTrace (prefixWord ++ tailWord_531735) baseStart_531735 baseEnd_531735 := by
    simpa [prefixWord, tailWord_531735, baseEnd_531735] using wordTrace_append hprefix tailTrace_531735
  have hstable : (prefixWord ++ tailWord_531735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531735).length < 2 ^ (prefixWord ++ tailWord_531735).sum := by decide
  have hdescent : baseEnd_531735 < baseStart_531735 := by decide
  rcases family_descends (prefixWord ++ tailWord_531735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531736 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_531736 : Nat := 118140960795 + 531736 * 2 ^ 59
def prefixEnd_531736 : Nat := 4983230072969 + 3 ^ 40 * 531736 * 2
def baseEnd_531736 : Nat := 273036149299236814154597

theorem tailTrace_531736 : CollatzResearch.WordTrace tailWord_531736 prefixEnd_531736 273036149299236814154597 := by
  unfold tailWord_531736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697002600809380061947531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12929336801079173415930041 9697002600809380061947531)
  ·
    refine ⟨14545503901214070092921297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697002600809380061947531 14545503901214070092921297)
    ·
      refine ⟨10909127925910552569690973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14545503901214070092921297 10909127925910552569690973)
      ·
        refine ⟨4090922972216457213634115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10909127925910552569690973 4090922972216457213634115)
        ·
          refine ⟨6136384458324685820451173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090922972216457213634115 6136384458324685820451173)
          ·
            refine ⟨1150572085935878591334595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6136384458324685820451173 1150572085935878591334595)
            ·
              refine ⟨1725858128903817887001893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150572085935878591334595 1725858128903817887001893)
              ·
                refine ⟨323598399169465853812855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1725858128903817887001893 323598399169465853812855)
                ·
                  refine ⟨485397598754198780719283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323598399169465853812855 485397598754198780719283)
                  ·
                    refine ⟨728096398131298171078925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485397598754198780719283 728096398131298171078925)
                    ·
                      refine ⟨273036149299236814154597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728096398131298171078925 273036149299236814154597)
                      ·
                        rfl

theorem cell23_531736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_531736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531736 prefixEnd_531736 := by exact prefixLift 531736
  have htrace : WordTrace (prefixWord ++ tailWord_531736) baseStart_531736 baseEnd_531736 := by
    simpa [prefixWord, tailWord_531736, baseEnd_531736] using wordTrace_append hprefix tailTrace_531736
  have hstable : (prefixWord ++ tailWord_531736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531736).length < 2 ^ (prefixWord ++ tailWord_531736).sum := by decide
  have hdescent : baseEnd_531736 < baseStart_531736 := by decide
  rcases family_descends (prefixWord ++ tailWord_531736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_531745 : Nat := 118140960795 + 531745 * 2 ^ 59
def prefixEnd_531745 : Nat := 4983230072969 + 3 ^ 40 * 531745 * 2
def baseEnd_531745 : Nat := 273040770625127278942055

theorem tailTrace_531745 : CollatzResearch.WordTrace tailWord_531745 prefixEnd_531745 273040770625127278942055 := by
  unfold tailWord_531745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394333458586154660972689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12929555639057436440648459 19394333458586154660972689)
  ·
    refine ⟨14545750093939615995729517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19394333458586154660972689 14545750093939615995729517)
    ·
      refine ⟨5454656285227355998398569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14545750093939615995729517 5454656285227355998398569)
      ·
        refine ⟨4090992213920516998798927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5454656285227355998398569 4090992213920516998798927)
        ·
          refine ⟨6136488320880775498198391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090992213920516998798927 6136488320880775498198391)
          ·
            refine ⟨9204732481321163247297587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6136488320880775498198391 9204732481321163247297587)
            ·
              refine ⟨13807098721981744870946381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204732481321163247297587 13807098721981744870946381)
              ·
                refine ⟨5177662020743154326604893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13807098721981744870946381 5177662020743154326604893)
                ·
                  refine ⟨1941623257778682872476835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5177662020743154326604893 1941623257778682872476835)
                  ·
                    refine ⟨2912434886668024308715253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941623257778682872476835 2912434886668024308715253)
                    ·
                      refine ⟨273040770625127278942055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2912434886668024308715253 273040770625127278942055)
                      ·
                        rfl

theorem cell23_531745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_531745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531745 prefixEnd_531745 := by exact prefixLift 531745
  have htrace : WordTrace (prefixWord ++ tailWord_531745) baseStart_531745 baseEnd_531745 := by
    simpa [prefixWord, tailWord_531745, baseEnd_531745] using wordTrace_append hprefix tailTrace_531745
  have hstable : (prefixWord ++ tailWord_531745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531745).length < 2 ^ (prefixWord ++ tailWord_531745).sum := by decide
  have hdescent : baseEnd_531745 < baseStart_531745 := by decide
  rcases family_descends (prefixWord ++ tailWord_531745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531752 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_531752 : Nat := 118140960795 + 531752 * 2 ^ 59
def prefixEnd_531752 : Nat := 4983230072969 + 3 ^ 40 * 531752 * 2
def baseEnd_531752 : Nat := 91014788329902917184841

theorem tailTrace_531752 : CollatzResearch.WordTrace tailWord_531752 prefixEnd_531752 91014788329902917184841 := by
  unfold tailWord_531752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697294384780397428238755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12929725846373863237651673 9697294384780397428238755)
  ·
    refine ⟨14545941577170596142358133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697294384780397428238755 14545941577170596142358133)
    ·
      refine ⟨1363682022859743388346075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14545941577170596142358133 1363682022859743388346075)
      ·
        refine ⟨2045523034289615082519113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363682022859743388346075 2045523034289615082519113)
        ·
          refine ⟨1534142275717211311889335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045523034289615082519113 1534142275717211311889335)
          ·
            refine ⟨2301213413575816967834003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534142275717211311889335 2301213413575816967834003)
            ·
              refine ⟨3451820120363725451751005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301213413575816967834003 3451820120363725451751005)
              ·
                refine ⟨1294432545136397044406627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3451820120363725451751005 1294432545136397044406627)
                ·
                  refine ⟨1941648817704595566609941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294432545136397044406627 1941648817704595566609941)
                  ·
                    refine ⟨91014788329902917184841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1941648817704595566609941 91014788329902917184841)
                    ·
                      rfl

theorem cell23_531752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_531752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531752 prefixEnd_531752 := by exact prefixLift 531752
  have htrace : WordTrace (prefixWord ++ tailWord_531752) baseStart_531752 baseEnd_531752 := by
    simpa [prefixWord, tailWord_531752, baseEnd_531752] using wordTrace_append hprefix tailTrace_531752
  have hstable : (prefixWord ++ tailWord_531752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531752).length < 2 ^ (prefixWord ++ tailWord_531752).sum := by decide
  have hdescent : baseEnd_531752 < baseStart_531752 := by decide
  rcases family_descends (prefixWord ++ tailWord_531752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531772 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_531772 : Nat := 118140960795 + 531772 * 2 ^ 59
def prefixEnd_531772 : Nat := 4983230072969 + 3 ^ 40 * 531772 * 2
def baseEnd_531772 : Nat := 273054634602798673304431

theorem tailTrace_531772 : CollatzResearch.WordTrace tailWord_531772 prefixEnd_531772 273054634602798673304431 := by
  unfold tailWord_531772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697659114744169136102785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12930212152992225514803713 9697659114744169136102785)
  ·
    refine ⟨7273244336058126852077089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9697659114744169136102785 7273244336058126852077089)
    ·
      refine ⟨5454933252043595139057817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7273244336058126852077089 5454933252043595139057817)
      ·
        refine ⟨4091199939032696354293363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5454933252043595139057817 4091199939032696354293363)
        ·
          refine ⟨6136799908549044531440045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091199939032696354293363 6136799908549044531440045)
          ·
            refine ⟨2301299965705891699290017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6136799908549044531440045 2301299965705891699290017)
            ·
              refine ⟨1725974974279418774467513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301299965705891699290017 1725974974279418774467513)
              ·
                refine ⟨1294481230709564080850635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725974974279418774467513 1294481230709564080850635)
                ·
                  refine ⟨1941721846064346121275953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294481230709564080850635 1941721846064346121275953)
                  ·
                    refine ⟨1456291384548259590956965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941721846064346121275953 1456291384548259590956965)
                    ·
                      refine ⟨273054634602798673304431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1456291384548259590956965 273054634602798673304431)
                      ·
                        rfl

theorem cell23_531772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_531772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531772 prefixEnd_531772 := by exact prefixLift 531772
  have htrace : WordTrace (prefixWord ++ tailWord_531772) baseStart_531772 baseEnd_531772 := by
    simpa [prefixWord, tailWord_531772, baseEnd_531772] using wordTrace_append hprefix tailTrace_531772
  have hstable : (prefixWord ++ tailWord_531772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531772).length < 2 ^ (prefixWord ++ tailWord_531772).sum := by decide
  have hdescent : baseEnd_531772 < baseStart_531772 := by decide
  rcases family_descends (prefixWord ++ tailWord_531772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531773 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_531773 : Nat := 118140960795 + 531773 * 2 ^ 59
def prefixEnd_531773 : Nat := 4983230072969 + 3 ^ 40 * 531773 * 2
def baseEnd_531773 : Nat := 91018382694484389797309

theorem tailTrace_531773 : CollatzResearch.WordTrace tailWord_531773 prefixEnd_531773 91018382694484389797309 := by
  unfold tailWord_531773
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395354702484715442991973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12930236468323143628661315 19395354702484715442991973)
  ·
    refine ⟨3636629006715884145560995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19395354702484715442991973 3636629006715884145560995)
    ·
      refine ⟨5454943510073826218341493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3636629006715884145560995 5454943510073826218341493)
      ·
        refine ⟨511400954069421207969515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5454943510073826218341493 511400954069421207969515)
        ·
          refine ⟨767101431104131811954273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511400954069421207969515 767101431104131811954273)
          ·
            refine ⟨575326073328098858965705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767101431104131811954273 575326073328098858965705)
            ·
              refine ⟨431494554996074144224279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575326073328098858965705 431494554996074144224279)
              ·
                refine ⟨647241832494111216336419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431494554996074144224279 647241832494111216336419)
                ·
                  refine ⟨970862748741166824504629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647241832494111216336419 970862748741166824504629)
                  ·
                    refine ⟨91018382694484389797309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 970862748741166824504629 91018382694484389797309)
                    ·
                      rfl

theorem cell23_531773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_531773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531773 prefixEnd_531773 := by exact prefixLift 531773
  have htrace : WordTrace (prefixWord ++ tailWord_531773) baseStart_531773 baseEnd_531773 := by
    simpa [prefixWord, tailWord_531773, baseEnd_531773] using wordTrace_append hprefix tailTrace_531773
  have hstable : (prefixWord ++ tailWord_531773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531773).length < 2 ^ (prefixWord ++ tailWord_531773).sum := by decide
  have hdescent : baseEnd_531773 < baseStart_531773 := by decide
  rcases family_descends (prefixWord ++ tailWord_531773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531809 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_531809 : Nat := 118140960795 + 531809 * 2 ^ 59
def prefixEnd_531809 : Nat := 4983230072969 + 3 ^ 40 * 531809 * 2
def baseEnd_531809 : Nat := 273073633387015028541761

theorem tailTrace_531809 : CollatzResearch.WordTrace tailWord_531809 prefixEnd_531809 273073633387015028541761 := by
  unfold tailWord_531809
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396667730354293591302481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12931111820236195727534987 19396667730354293591302481)
  ·
    refine ⟨14547500797765720193476861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19396667730354293591302481 14547500797765720193476861)
    ·
      refine ⟨5455312799162145072553823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14547500797765720193476861 5455312799162145072553823)
      ·
        refine ⟨8182969198743217608830735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5455312799162145072553823 8182969198743217608830735)
        ·
          refine ⟨12274453798114826413246103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8182969198743217608830735 12274453798114826413246103)
          ·
            refine ⟨18411680697172239619869155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12274453798114826413246103 18411680697172239619869155)
            ·
              refine ⟨27617521045758359429803733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18411680697172239619869155 27617521045758359429803733)
              ·
                refine ⟨647285649509961549136025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27617521045758359429803733 647285649509961549136025)
                ·
                  refine ⟨485464237132471161852019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647285649509961549136025 485464237132471161852019)
                  ·
                    refine ⟨728196355698706742778029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485464237132471161852019 728196355698706742778029)
                    ·
                      refine ⟨273073633387015028541761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728196355698706742778029 273073633387015028541761)
                      ·
                        rfl

theorem cell23_531809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_531809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531809 prefixEnd_531809 := by exact prefixLift 531809
  have htrace : WordTrace (prefixWord ++ tailWord_531809) baseStart_531809 baseEnd_531809 := by
    simpa [prefixWord, tailWord_531809, baseEnd_531809] using wordTrace_append hprefix tailTrace_531809
  have hstable : (prefixWord ++ tailWord_531809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531809).length < 2 ^ (prefixWord ++ tailWord_531809).sum := by decide
  have hdescent : baseEnd_531809 < baseStart_531809 := by decide
  rcases family_descends (prefixWord ++ tailWord_531809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531816 : List Nat := [2, 1, 4, 2, 4, 1, 2, 7]
def baseStart_531816 : Nat := 118140960795 + 531816 * 2 ^ 59
def prefixEnd_531816 : Nat := 4983230072969 + 3 ^ 40 * 531816 * 2
def baseEnd_531816 : Nat := 10113971398207277820527

theorem tailTrace_531816 : CollatzResearch.WordTrace tailWord_531816 prefixEnd_531816 10113971398207277820527 := by
  unfold tailWord_531816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698461520664466893403651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12931282027552622524538201 9698461520664466893403651)
  ·
    refine ⟨14547692280996700340105477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9698461520664466893403651 14547692280996700340105477)
    ·
      refine ⟨2727692302686881313769777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14547692280996700340105477 2727692302686881313769777)
      ·
        refine ⟨2045769227015160985327333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727692302686881313769777 2045769227015160985327333)
        ·
          refine ⟨383581730065342684748875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2045769227015160985327333 383581730065342684748875)
          ·
            refine ⟨575372595098014027123313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383581730065342684748875 575372595098014027123313)
            ·
              refine ⟨431529446323510520342485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575372595098014027123313 431529446323510520342485)
              ·
                refine ⟨10113971398207277820527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431529446323510520342485 10113971398207277820527)
                ·
                  rfl

theorem cell23_531816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 7].length) (baseStart_531816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531816 prefixEnd_531816 := by exact prefixLift 531816
  have htrace : WordTrace (prefixWord ++ tailWord_531816) baseStart_531816 baseEnd_531816 := by
    simpa [prefixWord, tailWord_531816, baseEnd_531816] using wordTrace_append hprefix tailTrace_531816
  have hstable : (prefixWord ++ tailWord_531816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531816).length < 2 ^ (prefixWord ++ tailWord_531816).sum := by decide
  have hdescent : baseEnd_531816 < baseStart_531816 := by decide
  rcases family_descends (prefixWord ++ tailWord_531816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531825 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_531825 : Nat := 118140960795 + 531825 * 2 ^ 59
def prefixEnd_531825 : Nat := 4983230072969 + 3 ^ 40 * 531825 * 2
def baseEnd_531825 : Nat := 91027283025828988647229

theorem tailTrace_531825 : CollatzResearch.WordTrace tailWord_531825 prefixEnd_531825 91027283025828988647229 := by
  unfold tailWord_531825
  simp only [CollatzResearch.WordTrace]
  refine ⟨19397251298296328323884929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12931500865530885549256619 19397251298296328323884929)
  ·
    refine ⟨14547938473722246242913697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19397251298296328323884929 14547938473722246242913697)
    ·
      refine ⟨10910953855291684682185273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14547938473722246242913697 10910953855291684682185273)
      ·
        refine ⟨8183215391468763511638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10910953855291684682185273 8183215391468763511638955)
        ·
          refine ⟨12274823087203145267458433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183215391468763511638955 12274823087203145267458433)
          ·
            refine ⟨9206117315402358950593825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12274823087203145267458433 9206117315402358950593825)
            ·
              refine ⟨6904587986551769212945369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9206117315402358950593825 6904587986551769212945369)
              ·
                refine ⟨5178440989913826909709027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904587986551769212945369 5178440989913826909709027)
                ·
                  refine ⟨7767661484870740364563541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178440989913826909709027 7767661484870740364563541)
                  ·
                    refine ⟨91027283025828988647229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7767661484870740364563541 91027283025828988647229)
                    ·
                      rfl

theorem cell23_531825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_531825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531825 prefixEnd_531825 := by exact prefixLift 531825
  have htrace : WordTrace (prefixWord ++ tailWord_531825) baseStart_531825 baseEnd_531825 := by
    simpa [prefixWord, tailWord_531825, baseEnd_531825] using wordTrace_append hprefix tailTrace_531825
  have hstable : (prefixWord ++ tailWord_531825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531825).length < 2 ^ (prefixWord ++ tailWord_531825).sum := by decide
  have hdescent : baseEnd_531825 < baseStart_531825 := by decide
  rcases family_descends (prefixWord ++ tailWord_531825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531852 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_531852 : Nat := 118140960795 + 531852 * 2 ^ 59
def prefixEnd_531852 : Nat := 4983230072969 + 3 ^ 40 * 531852 * 2
def baseEnd_531852 : Nat := 273095713055158360304063

theorem tailTrace_531852 : CollatzResearch.WordTrace tailWord_531852 prefixEnd_531852 273095713055158360304063 := by
  unfold tailWord_531852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699118034599255967558905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12932157379465674623411873 9699118034599255967558905)
  ·
    refine ⟨7274338525949441975669179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9699118034599255967558905 7274338525949441975669179)
    ·
      refine ⟨10911507788924162963503769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7274338525949441975669179 10911507788924162963503769)
      ·
        refine ⟨8183630841693122222627827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10911507788924162963503769 8183630841693122222627827)
        ·
          refine ⟨12275446262539683333941741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183630841693122222627827 12275446262539683333941741)
          ·
            refine ⟨4603292348452381250228153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12275446262539683333941741 4603292348452381250228153)
            ·
              refine ⟨3452469261339285937671115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603292348452381250228153 3452469261339285937671115)
              ·
                refine ⟨5178703892008928906506673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452469261339285937671115 5178703892008928906506673)
                ·
                  refine ⟨3884027919006696679880005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178703892008928906506673 3884027919006696679880005)
                  ·
                    refine ⟨728255234813755627477501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3884027919006696679880005 728255234813755627477501)
                    ·
                      refine ⟨273095713055158360304063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728255234813755627477501 273095713055158360304063)
                      ·
                        rfl

theorem cell23_531852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_531852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531852 prefixEnd_531852 := by exact prefixLift 531852
  have htrace : WordTrace (prefixWord ++ tailWord_531852) baseStart_531852 baseEnd_531852 := by
    simpa [prefixWord, tailWord_531852, baseEnd_531852] using wordTrace_append hprefix tailTrace_531852
  have hstable : (prefixWord ++ tailWord_531852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531852).length < 2 ^ (prefixWord ++ tailWord_531852).sum := by decide
  have hdescent : baseEnd_531852 < baseStart_531852 := by decide
  rcases family_descends (prefixWord ++ tailWord_531852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531860 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_531860 : Nat := 118140960795 + 531860 * 2 ^ 59
def prefixEnd_531860 : Nat := 4983230072969 + 3 ^ 40 * 531860 * 2
def baseEnd_531860 : Nat := 273099820900394329004027

theorem tailTrace_531860 : CollatzResearch.WordTrace tailWord_531860 prefixEnd_531860 273099820900394329004027 := by
  unfold tailWord_531860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699263926584764650704517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12932351902113019534272689 9699263926584764650704517)
  ·
    refine ⟨1818611986234643372007097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9699263926584764650704517 1818611986234643372007097)
    ·
      refine ⟨1363958989675982529005323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1818611986234643372007097 1363958989675982529005323)
      ·
        refine ⟨2045938484513973793507985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363958989675982529005323 2045938484513973793507985)
        ·
          refine ⟨1534453863385480345130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045938484513973793507985 1534453863385480345130989)
          ·
            refine ⟨575420198769555129424121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1534453863385480345130989 575420198769555129424121)
            ·
              refine ⟨431565149077166347068091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575420198769555129424121 431565149077166347068091)
              ·
                refine ⟨647347723615749520602137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431565149077166347068091 647347723615749520602137)
                ·
                  refine ⟨485510792711812140451603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647347723615749520602137 485510792711812140451603)
                  ·
                    refine ⟨728266189067718210677405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485510792711812140451603 728266189067718210677405)
                    ·
                      refine ⟨273099820900394329004027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728266189067718210677405 273099820900394329004027)
                      ·
                        rfl

theorem cell23_531860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_531860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531860 prefixEnd_531860 := by exact prefixLift 531860
  have htrace : WordTrace (prefixWord ++ tailWord_531860) baseStart_531860 baseEnd_531860 := by
    simpa [prefixWord, tailWord_531860, baseEnd_531860] using wordTrace_append hprefix tailTrace_531860
  have hstable : (prefixWord ++ tailWord_531860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531860).length < 2 ^ (prefixWord ++ tailWord_531860).sum := by decide
  have hdescent : baseEnd_531860 < baseStart_531860 := by decide
  rcases family_descends (prefixWord ++ tailWord_531860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531889 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 5]
def baseStart_531889 : Nat := 118140960795 + 531889 * 2 ^ 59
def prefixEnd_531889 : Nat := 4983230072969 + 3 ^ 40 * 531889 * 2
def baseEnd_531889 : Nat := 30346079093263857282377

theorem tailTrace_531889 : CollatzResearch.WordTrace tailWord_531889 prefixEnd_531889 30346079093263857282377 := by
  unfold tailWord_531889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399585570064467254214721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12933057046709644836143147 19399585570064467254214721)
  ·
    refine ⟨14549689177548350440661041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19399585570064467254214721 14549689177548350440661041)
    ·
      refine ⟨10912266883161262830495781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14549689177548350440661041 10912266883161262830495781)
      ·
        refine ⟨2046050040592736780717959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10912266883161262830495781 2046050040592736780717959)
        ·
          refine ⟨3069075060889105171076939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2046050040592736780717959 3069075060889105171076939)
          ·
            refine ⟨4603612591333657756615409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069075060889105171076939 4603612591333657756615409)
            ·
              refine ⟨3452709443500243317461557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4603612591333657756615409 3452709443500243317461557)
              ·
                refine ⟨323691510328147811012021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3452709443500243317461557 323691510328147811012021)
                ·
                  refine ⟨30346079093263857282377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323691510328147811012021 30346079093263857282377)
                  ·
                    rfl

theorem cell23_531889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 5].length) (baseStart_531889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531889 prefixEnd_531889 := by exact prefixLift 531889
  have htrace : WordTrace (prefixWord ++ tailWord_531889) baseStart_531889 baseEnd_531889 := by
    simpa [prefixWord, tailWord_531889, baseEnd_531889] using wordTrace_append hprefix tailTrace_531889
  have hstable : (prefixWord ++ tailWord_531889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531889).length < 2 ^ (prefixWord ++ tailWord_531889).sum := by decide
  have hdescent : baseEnd_531889 < baseStart_531889 := by decide
  rcases family_descends (prefixWord ++ tailWord_531889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531900 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_531900 : Nat := 118140960795 + 531900 * 2 ^ 59
def prefixEnd_531900 : Nat := 4983230072969 + 3 ^ 40 * 531900 * 2
def baseEnd_531900 : Nat := 273120360126574172503843

theorem tailTrace_531900 : CollatzResearch.WordTrace tailWord_531900 prefixEnd_531900 273120360126574172503843 := by
  unfold tailWord_531900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699993386512308066432577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12933324515349744088576769 9699993386512308066432577)
  ·
    refine ⟨7274995039884231049824433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9699993386512308066432577 7274995039884231049824433)
    ·
      refine ⟨5456246279913173287368325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7274995039884231049824433 5456246279913173287368325)
      ·
        refine ⟨1023046177483719991381561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5456246279913173287368325 1023046177483719991381561)
        ·
          refine ⟨767284633112789993536171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023046177483719991381561 767284633112789993536171)
          ·
            refine ⟨1150926949669184990304257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767284633112789993536171 1150926949669184990304257)
            ·
              refine ⟨863195212251888742728193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150926949669184990304257 863195212251888742728193)
              ·
                refine ⟨647396409188916557046145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863195212251888742728193 647396409188916557046145)
                ·
                  refine ⟨485547306891687417784609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 647396409188916557046145 485547306891687417784609)
                  ·
                    refine ⟨364160480168765563338457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 485547306891687417784609 364160480168765563338457)
                    ·
                      refine ⟨273120360126574172503843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364160480168765563338457 273120360126574172503843)
                      ·
                        rfl

theorem cell23_531900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_531900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531900 prefixEnd_531900 := by exact prefixLift 531900
  have htrace : WordTrace (prefixWord ++ tailWord_531900) baseStart_531900 baseEnd_531900 := by
    simpa [prefixWord, tailWord_531900, baseEnd_531900] using wordTrace_append hprefix tailTrace_531900
  have hstable : (prefixWord ++ tailWord_531900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531900).length < 2 ^ (prefixWord ++ tailWord_531900).sum := by decide
  have hdescent : baseEnd_531900 < baseStart_531900 := by decide
  rcases family_descends (prefixWord ++ tailWord_531900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531902 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_531902 : Nat := 118140960795 + 531902 * 2 ^ 59
def prefixEnd_531902 : Nat := 4983230072969 + 3 ^ 40 * 531902 * 2
def baseEnd_531902 : Nat := 91040462362627721559611

theorem tailTrace_531902 : CollatzResearch.WordTrace tailWord_531902 prefixEnd_531902 91040462362627721559611 := by
  unfold tailWord_531902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425007464877171309304745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12933373146011580316291973 2425007464877171309304745)
  ·
    refine ⟨1818755598657878481978559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2425007464877171309304745 1818755598657878481978559)
    ·
      refine ⟨2728133397986817722967839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818755598657878481978559 2728133397986817722967839)
      ·
        refine ⟨4092200096980226584451759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728133397986817722967839 4092200096980226584451759)
        ·
          refine ⟨6138300145470339876677639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092200096980226584451759 6138300145470339876677639)
          ·
            refine ⟨9207450218205509815016459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6138300145470339876677639 9207450218205509815016459)
            ·
              refine ⟨13811175327308264722524689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207450218205509815016459 13811175327308264722524689)
              ·
                refine ⟨10358381495481198541893517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13811175327308264722524689 10358381495481198541893517)
                ·
                  refine ⟨3884393060805449453210069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10358381495481198541893517 3884393060805449453210069)
                  ·
                    refine ⟨91040462362627721559611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3884393060805449453210069 91040462362627721559611)
                    ·
                      rfl

theorem cell23_531902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_531902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531902 prefixEnd_531902 := by exact prefixLift 531902
  have htrace : WordTrace (prefixWord ++ tailWord_531902) baseStart_531902 baseEnd_531902 := by
    simpa [prefixWord, tailWord_531902, baseEnd_531902] using wordTrace_append hprefix tailTrace_531902
  have hstable : (prefixWord ++ tailWord_531902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531902).length < 2 ^ (prefixWord ++ tailWord_531902).sum := by decide
  have hdescent : baseEnd_531902 < baseStart_531902 := by decide
  rcases family_descends (prefixWord ++ tailWord_531902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531912 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_531912 : Nat := 118140960795 + 531912 * 2 ^ 59
def prefixEnd_531912 : Nat := 4983230072969 + 3 ^ 40 * 531912 * 2
def baseEnd_531912 : Nat := 273126521894428125553787

theorem tailTrace_531912 : CollatzResearch.WordTrace tailWord_531912 prefixEnd_531912 273126521894428125553787 := by
  unfold tailWord_531912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700212224490571091150995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12933616299320761454867993 9700212224490571091150995)
  ·
    refine ⟨14550318336735856636726493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700212224490571091150995 14550318336735856636726493)
    ·
      refine ⟨5456369376275946238772435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14550318336735856636726493 5456369376275946238772435)
      ·
        refine ⟨8184554064413919358158653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456369376275946238772435 8184554064413919358158653)
        ·
          refine ⟨3069207774155219759309495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8184554064413919358158653 3069207774155219759309495)
          ·
            refine ⟨4603811661232829638964243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069207774155219759309495 4603811661232829638964243)
            ·
              refine ⟨6905717491849244458446365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603811661232829638964243 6905717491849244458446365)
              ·
                refine ⟨2589644059443466671917387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6905717491849244458446365 2589644059443466671917387)
                ·
                  refine ⟨3884466089165200007876081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589644059443466671917387 3884466089165200007876081)
                  ·
                    refine ⟨2913349566873900005907061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884466089165200007876081 2913349566873900005907061)
                    ·
                      refine ⟨273126521894428125553787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2913349566873900005907061 273126521894428125553787)
                      ·
                        rfl

theorem cell23_531912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_531912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531912 prefixEnd_531912 := by exact prefixLift 531912
  have htrace : WordTrace (prefixWord ++ tailWord_531912) baseStart_531912 baseEnd_531912 := by
    simpa [prefixWord, tailWord_531912, baseEnd_531912] using wordTrace_append hprefix tailTrace_531912
  have hstable : (prefixWord ++ tailWord_531912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531912).length < 2 ^ (prefixWord ++ tailWord_531912).sum := by decide
  have hdescent : baseEnd_531912 < baseStart_531912 := by decide
  rcases family_descends (prefixWord ++ tailWord_531912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531939 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_531939 : Nat := 118140960795 + 531939 * 2 ^ 59
def prefixEnd_531939 : Nat := 4983230072969 + 3 ^ 40 * 531939 * 2
def baseEnd_531939 : Nat := 273140385872099519916163

theorem tailTrace_531939 : CollatzResearch.WordTrace tailWord_531939 prefixEnd_531939 273140385872099519916163 := by
  unfold tailWord_531939
  simp only [CollatzResearch.WordTrace]
  refine ⟨19401409219883325793534871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12934272813255550529023247 19401409219883325793534871)
  ·
    refine ⟨29102113829824988690302307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19401409219883325793534871 29102113829824988690302307)
    ·
      refine ⟨43653170744737483035453461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29102113829824988690302307 43653170744737483035453461)
      ·
        refine ⟨2046242378659569517286881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43653170744737483035453461 2046242378659569517286881)
        ·
          refine ⟨1534681783994677137965161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046242378659569517286881 1534681783994677137965161)
          ·
            refine ⟨1151011337996007853473871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534681783994677137965161 1151011337996007853473871)
            ·
              refine ⟨1726517006994011780210807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151011337996007853473871 1726517006994011780210807)
              ·
                refine ⟨2589775510491017670316211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726517006994011780210807 2589775510491017670316211)
                ·
                  refine ⟨3884663265736526505474317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589775510491017670316211 3884663265736526505474317)
                  ·
                    refine ⟨1456748724651197439552869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3884663265736526505474317 1456748724651197439552869)
                    ·
                      refine ⟨273140385872099519916163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1456748724651197439552869 273140385872099519916163)
                      ·
                        rfl

theorem cell23_531939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_531939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531939 prefixEnd_531939 := by exact prefixLift 531939
  have htrace : WordTrace (prefixWord ++ tailWord_531939) baseStart_531939 baseEnd_531939 := by
    simpa [prefixWord, tailWord_531939, baseEnd_531939] using wordTrace_append hprefix tailTrace_531939
  have hstable : (prefixWord ++ tailWord_531939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531939).length < 2 ^ (prefixWord ++ tailWord_531939).sum := by decide
  have hdescent : baseEnd_531939 < baseStart_531939 := by decide
  rcases family_descends (prefixWord ++ tailWord_531939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531952 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_531952 : Nat := 118140960795 + 531952 * 2 ^ 59
def prefixEnd_531952 : Nat := 4983230072969 + 3 ^ 40 * 531952 * 2
def baseEnd_531952 : Nat := 273147061120607969053603

theorem tailTrace_531952 : CollatzResearch.WordTrace tailWord_531952 prefixEnd_531952 273147061120607969053603 := by
  unfold tailWord_531952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700941684418114506879055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12934588912557486009172073 9700941684418114506879055)
  ·
    refine ⟨14551412526627171760318583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700941684418114506879055 14551412526627171760318583)
    ·
      refine ⟨21827118789940757640477875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14551412526627171760318583 21827118789940757640477875)
      ·
        refine ⟨32740678184911136460716813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21827118789940757640477875 32740678184911136460716813)
        ·
          refine ⟨12277754319341676172768805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32740678184911136460716813 12277754319341676172768805)
          ·
            refine ⟨2302078934876564282394151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12277754319341676172768805 2302078934876564282394151)
            ·
              refine ⟨3453118402314846423591227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302078934876564282394151 3453118402314846423591227)
              ·
                refine ⟨5179677603472269635386841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453118402314846423591227 5179677603472269635386841)
                ·
                  refine ⟨3884758202604202226540131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179677603472269635386841 3884758202604202226540131)
                  ·
                    refine ⟨5827137303906303339810197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884758202604202226540131 5827137303906303339810197)
                    ·
                      refine ⟨273147061120607969053603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5827137303906303339810197 273147061120607969053603)
                      ·
                        rfl

theorem cell23_531952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_531952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531952 prefixEnd_531952 := by exact prefixLift 531952
  have htrace : WordTrace (prefixWord ++ tailWord_531952) baseStart_531952 baseEnd_531952 := by
    simpa [prefixWord, tailWord_531952, baseEnd_531952] using wordTrace_append hprefix tailTrace_531952
  have hstable : (prefixWord ++ tailWord_531952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531952).length < 2 ^ (prefixWord ++ tailWord_531952).sum := by decide
  have hdescent : baseEnd_531952 < baseStart_531952 := by decide
  rcases family_descends (prefixWord ++ tailWord_531952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_531962 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_531962 : Nat := 118140960795 + 531962 * 2 ^ 59
def prefixEnd_531962 : Nat := 4983230072969 + 3 ^ 40 * 531962 * 2
def baseEnd_531962 : Nat := 30350243991905881103173

theorem tailTrace_531962 : CollatzResearch.WordTrace tailWord_531962 prefixEnd_531962 30350243991905881103173 := by
  unfold tailWord_531962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850562024700000180405535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12934832065866667147748093 4850562024700000180405535)
  ·
    refine ⟨7275843037050000270608303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4850562024700000180405535 7275843037050000270608303)
    ·
      refine ⟨10913764555575000405912455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7275843037050000270608303 10913764555575000405912455)
      ·
        refine ⟨16370646833362500608868683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10913764555575000405912455 16370646833362500608868683)
        ·
          refine ⟨24555970250043750913303025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16370646833362500608868683 24555970250043750913303025)
          ·
            refine ⟨18416977687532813184977269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24555970250043750913303025 18416977687532813184977269)
            ·
              refine ⟨1726591658206201236091619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18416977687532813184977269 1726591658206201236091619)
              ·
                refine ⟨2589887487309301854137429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726591658206201236091619 2589887487309301854137429)
                ·
                  refine ⟨30350243991905881103173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2589887487309301854137429 30350243991905881103173)
                  ·
                    rfl

theorem cell23_531962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_531962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_531962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_531962 prefixEnd_531962 := by exact prefixLift 531962
  have htrace : WordTrace (prefixWord ++ tailWord_531962) baseStart_531962 baseEnd_531962 := by
    simpa [prefixWord, tailWord_531962, baseEnd_531962] using wordTrace_append hprefix tailTrace_531962
  have hstable : (prefixWord ++ tailWord_531962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_531962).length < 2 ^ (prefixWord ++ tailWord_531962).sum := by decide
  have hdescent : baseEnd_531962 < baseStart_531962 := by decide
  rcases family_descends (prefixWord ++ tailWord_531962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532000 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 1, 4]
def baseStart_532000 : Nat := 118140960795 + 532000 * 2 ^ 59
def prefixEnd_532000 : Nat := 4983230072969 + 3 ^ 40 * 532000 * 2
def baseEnd_532000 : Nat := 91057236064007927084461

theorem tailTrace_532000 : CollatzResearch.WordTrace tailWord_532000 prefixEnd_532000 91057236064007927084461 := by
  unfold tailWord_532000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9701817036331166605752727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12935756048441555474336969 9701817036331166605752727)
  ·
    refine ⟨14552725554496749908629091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9701817036331166605752727 14552725554496749908629091)
    ·
      refine ⟨21829088331745124862943637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14552725554496749908629091 21829088331745124862943637)
      ·
        refine ⟨1023238515550552727950483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21829088331745124862943637 1023238515550552727950483)
        ·
          refine ⟨1534857773325829091925725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023238515550552727950483 1534857773325829091925725)
          ·
            refine ⟨575571664997185909472147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1534857773325829091925725 575571664997185909472147)
            ·
              refine ⟨863357497495778864208221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575571664997185909472147 863357497495778864208221)
              ·
                refine ⟨323759061560917074078083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863357497495778864208221 323759061560917074078083)
                ·
                  refine ⟨485638592341375611117125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323759061560917074078083 485638592341375611117125)
                  ·
                    refine ⟨91057236064007927084461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485638592341375611117125 91057236064007927084461)
                    ·
                      rfl

theorem cell23_532000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_532000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532000 prefixEnd_532000 := by exact prefixLift 532000
  have htrace : WordTrace (prefixWord ++ tailWord_532000) baseStart_532000 baseEnd_532000 := by
    simpa [prefixWord, tailWord_532000, baseEnd_532000] using wordTrace_append hprefix tailTrace_532000
  have hstable : (prefixWord ++ tailWord_532000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532000).length < 2 ^ (prefixWord ++ tailWord_532000).sum := by decide
  have hdescent : baseEnd_532000 < baseStart_532000 := by decide
  rcases family_descends (prefixWord ++ tailWord_532000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532023 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_532023 : Nat := 118140960795 + 532023 * 2 ^ 59
def prefixEnd_532023 : Nat := 4983230072969 + 3 ^ 40 * 532023 * 2
def baseEnd_532023 : Nat := 273183518247077191265777

theorem tailTrace_532023 : CollatzResearch.WordTrace tailWord_532023 prefixEnd_532023 273183518247077191265777 := by
  unfold tailWord_532023
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404472951579008139592723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12936315301052672093061815 19404472951579008139592723)
  ·
    refine ⟨29106709427368512209389085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404472951579008139592723 29106709427368512209389085)
    ·
      refine ⟨10915016035263192078520907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29106709427368512209389085 10915016035263192078520907)
      ·
        refine ⟨16372524052894788117781361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10915016035263192078520907 16372524052894788117781361)
        ·
          refine ⟨12279393039671091088336021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16372524052894788117781361 12279393039671091088336021)
          ·
            refine ⟨575596548734582394765751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12279393039671091088336021 575596548734582394765751)
            ·
              refine ⟨863394823101873592148627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575596548734582394765751 863394823101873592148627)
              ·
                refine ⟨1295092234652810388222941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863394823101873592148627 1295092234652810388222941)
                ·
                  refine ⟨485659587994803895583603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1295092234652810388222941 485659587994803895583603)
                  ·
                    refine ⟨728489381992205843375405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485659587994803895583603 728489381992205843375405)
                    ·
                      refine ⟨273183518247077191265777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728489381992205843375405 273183518247077191265777)
                      ·
                        rfl

theorem cell23_532023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_532023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532023 prefixEnd_532023 := by exact prefixLift 532023
  have htrace : WordTrace (prefixWord ++ tailWord_532023) baseStart_532023 baseEnd_532023 := by
    simpa [prefixWord, tailWord_532023, baseEnd_532023] using wordTrace_append hprefix tailTrace_532023
  have hstable : (prefixWord ++ tailWord_532023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532023).length < 2 ^ (prefixWord ++ tailWord_532023).sum := by decide
  have hdescent : baseEnd_532023 < baseStart_532023 := by decide
  rcases family_descends (prefixWord ++ tailWord_532023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532079 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_532079 : Nat := 118140960795 + 532079 * 2 ^ 59
def prefixEnd_532079 : Nat := 4983230072969 + 3 ^ 40 * 532079 * 2
def baseEnd_532079 : Nat := 273212273163728972165519

theorem tailTrace_532079 : CollatzResearch.WordTrace tailWord_532079 prefixEnd_532079 273212273163728972165519 := by
  unfold tailWord_532079
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406515439376129703631291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12937676959584086469087527 19406515439376129703631291)
  ·
    refine ⟨29109773159064194555446937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19406515439376129703631291 29109773159064194555446937)
    ·
      refine ⟨21832329869298145916585203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29109773159064194555446937 21832329869298145916585203)
      ·
        refine ⟨32748494803947218874877805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21832329869298145916585203 32748494803947218874877805)
        ·
          refine ⟨12280685551480207078079177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32748494803947218874877805 12280685551480207078079177)
          ·
            refine ⟨9210514163610155308559383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12280685551480207078079177 9210514163610155308559383)
            ·
              refine ⟨13815771245415232962839075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9210514163610155308559383 13815771245415232962839075)
              ·
                refine ⟨20723656868122849444258613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13815771245415232962839075 20723656868122849444258613)
                ·
                  refine ⟨1942842831386517135399245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20723656868122849444258613 1942842831386517135399245)
                  ·
                    refine ⟨728566061769943925774717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942842831386517135399245 728566061769943925774717)
                    ·
                      refine ⟨273212273163728972165519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728566061769943925774717 273212273163728972165519)
                      ·
                        rfl

theorem cell23_532079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_532079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532079 prefixEnd_532079 := by exact prefixLift 532079
  have htrace : WordTrace (prefixWord ++ tailWord_532079) baseStart_532079 baseEnd_532079 := by
    simpa [prefixWord, tailWord_532079, baseEnd_532079] using wordTrace_append hprefix tailTrace_532079
  have hstable : (prefixWord ++ tailWord_532079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532079).length < 2 ^ (prefixWord ++ tailWord_532079).sum := by decide
  have hdescent : baseEnd_532079 < baseStart_532079 := by decide
  rcases family_descends (prefixWord ++ tailWord_532079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532086 : List Nat := [5, 1, 1, 2, 2, 1, 3, 8]
def baseStart_532086 : Nat := 118140960795 + 532086 * 2 ^ 59
def prefixEnd_532086 : Nat := 4983230072969 + 3 ^ 40 * 532086 * 2
def baseEnd_532086 : Nat := 10119106204752238695481

theorem tailTrace_532086 : CollatzResearch.WordTrace tailWord_532086 prefixEnd_532086 10119106204752238695481 := by
  unfold tailWord_532086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212923171896923118696007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12937847166900513266090741 1212923171896923118696007)
  ·
    refine ⟨1819384757845384678044011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212923171896923118696007 1819384757845384678044011)
    ·
      refine ⟨2729077136768077017066017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819384757845384678044011 2729077136768077017066017)
      ·
        refine ⟨2046807852576057762799513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2729077136768077017066017 2046807852576057762799513)
        ·
          refine ⟨1535105889432043322099635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046807852576057762799513 1535105889432043322099635)
          ·
            refine ⟨2302658834148064983149453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535105889432043322099635 2302658834148064983149453)
            ·
              refine ⟨863497062805524368681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302658834148064983149453 863497062805524368681045)
              ·
                refine ⟨10119106204752238695481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 863497062805524368681045 10119106204752238695481)
                ·
                  rfl

theorem cell23_532086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_532086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532086 prefixEnd_532086 := by exact prefixLift 532086
  have htrace : WordTrace (prefixWord ++ tailWord_532086) baseStart_532086 baseEnd_532086 := by
    simpa [prefixWord, tailWord_532086, baseEnd_532086] using wordTrace_append hprefix tailTrace_532086
  have hstable : (prefixWord ++ tailWord_532086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532086).length < 2 ^ (prefixWord ++ tailWord_532086).sum := by decide
  have hdescent : baseEnd_532086 < baseStart_532086 := by decide
  rcases family_descends (prefixWord ++ tailWord_532086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532096 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_532096 : Nat := 118140960795 + 532096 * 2 ^ 59
def prefixEnd_532096 : Nat := 4983230072969 + 3 ^ 40 * 532096 * 2
def baseEnd_532096 : Nat := 273221002334855405652941

theorem tailTrace_532096 : CollatzResearch.WordTrace tailWord_532096 prefixEnd_532096 273221002334855405652941 := by
  unfold tailWord_532096
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703567740157270803500071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12938090320209694404666761 9703567740157270803500071)
  ·
    refine ⟨14555351610235906205250107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9703567740157270803500071 14555351610235906205250107)
    ·
      refine ⟨21833027415353859307875161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14555351610235906205250107 21833027415353859307875161)
      ·
        refine ⟨16374770561515394480906371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21833027415353859307875161 16374770561515394480906371)
        ·
          refine ⟨24562155842273091721359557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16374770561515394480906371 24562155842273091721359557)
          ·
            refine ⟨4605404220426204697754917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24562155842273091721359557 4605404220426204697754917)
            ·
              refine ⟨863513291329913380829047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4605404220426204697754917 863513291329913380829047)
              ·
                refine ⟨1295269936994870071243571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863513291329913380829047 1295269936994870071243571)
                ·
                  refine ⟨1942904905492305106865357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295269936994870071243571 1942904905492305106865357)
                  ·
                    refine ⟨728589339559614415074509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942904905492305106865357 728589339559614415074509)
                    ·
                      refine ⟨273221002334855405652941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728589339559614415074509 273221002334855405652941)
                      ·
                        rfl

theorem cell23_532096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_532096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532096 prefixEnd_532096 := by exact prefixLift 532096
  have htrace : WordTrace (prefixWord ++ tailWord_532096) baseStart_532096 baseEnd_532096 := by
    simpa [prefixWord, tailWord_532096, baseEnd_532096] using wordTrace_append hprefix tailTrace_532096
  have hstable : (prefixWord ++ tailWord_532096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532096).length < 2 ^ (prefixWord ++ tailWord_532096).sum := by decide
  have hdescent : baseEnd_532096 < baseStart_532096 := by decide
  rcases family_descends (prefixWord ++ tailWord_532096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532114 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_532114 : Nat := 118140960795 + 532114 * 2 ^ 59
def prefixEnd_532114 : Nat := 4983230072969 + 3 ^ 40 * 532114 * 2
def baseEnd_532114 : Nat := 273230244986636335227859

theorem tailTrace_532114 : CollatzResearch.WordTrace tailWord_532114 prefixEnd_532114 273230244986636335227859 := by
  unfold tailWord_532114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4851947998562332670288849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12938527996166220454103597 4851947998562332670288849)
  ·
    refine ⟨3638960998921749502716637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4851947998562332670288849 3638960998921749502716637)
    ·
      refine ⟨1364610374595656063518739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3638960998921749502716637 1364610374595656063518739)
      ·
        refine ⟨2046915561893484095278109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364610374595656063518739 2046915561893484095278109)
        ·
          refine ⟨767593335710056535729291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2046915561893484095278109 767593335710056535729291)
          ·
            refine ⟨1151390003565084803593937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767593335710056535729291 1151390003565084803593937)
            ·
              refine ⟨863542502673813602695453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151390003565084803593937 863542502673813602695453)
              ·
                refine ⟨323828438502680101010795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863542502673813602695453 323828438502680101010795)
                ·
                  refine ⟨485742657754020151516193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323828438502680101010795 485742657754020151516193)
                  ·
                    refine ⟨364306993315515113637145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 485742657754020151516193 364306993315515113637145)
                    ·
                      refine ⟨273230244986636335227859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364306993315515113637145 273230244986636335227859)
                      ·
                        rfl

theorem cell23_532114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_532114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532114 prefixEnd_532114 := by exact prefixLift 532114
  have htrace : WordTrace (prefixWord ++ tailWord_532114) baseStart_532114 baseEnd_532114 := by
    simpa [prefixWord, tailWord_532114, baseEnd_532114] using wordTrace_append hprefix tailTrace_532114
  have hstable : (prefixWord ++ tailWord_532114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532114).length < 2 ^ (prefixWord ++ tailWord_532114).sum := by decide
  have hdescent : baseEnd_532114 < baseStart_532114 := by decide
  rcases family_descends (prefixWord ++ tailWord_532114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532153 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 4, 2]
def baseStart_532153 : Nat := 118140960795 + 532153 * 2 ^ 59
def prefixEnd_532153 : Nat := 4983230072969 + 3 ^ 40 * 532153 * 2
def baseEnd_532153 : Nat := 273250270732161682640179

theorem tailTrace_532153 : CollatzResearch.WordTrace tailWord_532153 prefixEnd_532153 273250270732161682640179 := by
  unfold tailWord_532153
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409214441108040341825113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12939476294072026894550075 19409214441108040341825113)
  ·
    refine ⟨14556910830831030256368835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19409214441108040341825113 14556910830831030256368835)
    ·
      refine ⟨21835366246246545384553253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14556910830831030256368835 21835366246246545384553253)
      ·
        refine ⟨4094131171171227259603735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21835366246246545384553253 4094131171171227259603735)
        ·
          refine ⟨6141196756756840889405603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4094131171171227259603735 6141196756756840889405603)
          ·
            refine ⟨9211795135135261334108405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6141196756756840889405603 9211795135135261334108405)
            ·
              refine ⟨863605793918930750072663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9211795135135261334108405 863605793918930750072663)
              ·
                refine ⟨1295408690878396125108995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863605793918930750072663 1295408690878396125108995)
                ·
                  refine ⟨1943113036317594187663493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295408690878396125108995 1943113036317594187663493)
                  ·
                    refine ⟨364333694309548910186905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943113036317594187663493 364333694309548910186905)
                    ·
                      refine ⟨273250270732161682640179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364333694309548910186905 273250270732161682640179)
                      ·
                        rfl

theorem cell23_532153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_532153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532153 prefixEnd_532153 := by exact prefixLift 532153
  have htrace : WordTrace (prefixWord ++ tailWord_532153) baseStart_532153 baseEnd_532153 := by
    simpa [prefixWord, tailWord_532153, baseEnd_532153] using wordTrace_append hprefix tailTrace_532153
  have hstable : (prefixWord ++ tailWord_532153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532153).length < 2 ^ (prefixWord ++ tailWord_532153).sum := by decide
  have hdescent : baseEnd_532153 < baseStart_532153 := by decide
  rcases family_descends (prefixWord ++ tailWord_532153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532159 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 7]
def baseStart_532159 : Nat := 118140960795 + 532159 * 2 ^ 59
def prefixEnd_532159 : Nat := 4983230072969 + 3 ^ 40 * 532159 * 2
def baseEnd_532159 : Nat := 30361483512898739907239

theorem tailTrace_532159 : CollatzResearch.WordTrace tailWord_532159 prefixEnd_532159 30361483512898739907239 := by
  unfold tailWord_532159
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409433279086303366543531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12939622186057535577695687 19409433279086303366543531)
  ·
    refine ⟨29114149918629455049815297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19409433279086303366543531 29114149918629455049815297)
    ·
      refine ⟨21835612438972091287361473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29114149918629455049815297 21835612438972091287361473)
      ·
        refine ⟨16376709329229068465521105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21835612438972091287361473 16376709329229068465521105)
        ·
          refine ⟨12282531996921801349140829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16376709329229068465521105 12282531996921801349140829)
          ·
            refine ⟨4605949498845675505927811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12282531996921801349140829 4605949498845675505927811)
            ·
              refine ⟨6908924248268513258891717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605949498845675505927811 6908924248268513258891717)
              ·
                refine ⟨1295423296550346236042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6908924248268513258891717 1295423296550346236042197)
                ·
                  refine ⟨30361483512898739907239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1295423296550346236042197 30361483512898739907239)
                  ·
                    rfl

theorem cell23_532159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 7].length) (baseStart_532159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532159 prefixEnd_532159 := by exact prefixLift 532159
  have htrace : WordTrace (prefixWord ++ tailWord_532159) baseStart_532159 baseEnd_532159 := by
    simpa [prefixWord, tailWord_532159, baseEnd_532159] using wordTrace_append hprefix tailTrace_532159
  have hstable : (prefixWord ++ tailWord_532159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532159).length < 2 ^ (prefixWord ++ tailWord_532159).sum := by decide
  have hdescent : baseEnd_532159 < baseStart_532159 := by decide
  rcases family_descends (prefixWord ++ tailWord_532159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532173 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_532173 : Nat := 118140960795 + 532173 * 2 ^ 59
def prefixEnd_532173 : Nat := 4983230072969 + 3 ^ 40 * 532173 * 2
def baseEnd_532173 : Nat := 273260540345251604390087

theorem tailTrace_532173 : CollatzResearch.WordTrace tailWord_532173 prefixEnd_532173 273260540345251604390087 := by
  unfold tailWord_532173
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409943901035583757553173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12939962600690389171702115 19409943901035583757553173)
  ·
    refine ⟨909841120361042988635305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19409943901035583757553173 909841120361042988635305)
    ·
      refine ⟨682380840270782241476479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909841120361042988635305 682380840270782241476479)
      ·
        refine ⟨1023571260406173362214719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682380840270782241476479 1023571260406173362214719)
        ·
          refine ⟨1535356890609260043322079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023571260406173362214719 1535356890609260043322079)
          ·
            refine ⟨2303035335913890064983119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535356890609260043322079 2303035335913890064983119)
            ·
              refine ⟨3454553003870835097474679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303035335913890064983119 3454553003870835097474679)
              ·
                refine ⟨5181829505806252646212019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454553003870835097474679 5181829505806252646212019)
                ·
                  refine ⟨7772744258709378969318029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181829505806252646212019 7772744258709378969318029)
                  ·
                    refine ⟨2914779097016017113494261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7772744258709378969318029 2914779097016017113494261)
                    ·
                      refine ⟨273260540345251604390087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2914779097016017113494261 273260540345251604390087)
                      ·
                        rfl

theorem cell23_532173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_532173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532173 prefixEnd_532173 := by exact prefixLift 532173
  have htrace : WordTrace (prefixWord ++ tailWord_532173) baseStart_532173 baseEnd_532173 := by
    simpa [prefixWord, tailWord_532173, baseEnd_532173] using wordTrace_append hprefix tailTrace_532173
  have hstable : (prefixWord ++ tailWord_532173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532173).length < 2 ^ (prefixWord ++ tailWord_532173).sum := by decide
  have hdescent : baseEnd_532173 < baseStart_532173 := by decide
  rcases family_descends (prefixWord ++ tailWord_532173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532176 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 5]
def baseStart_532176 : Nat := 118140960795 + 532176 * 2 ^ 59
def prefixEnd_532176 : Nat := 4983230072969 + 3 ^ 40 * 532176 * 2
def baseEnd_532176 : Nat := 30362453420801676961397

theorem tailTrace_532176 : CollatzResearch.WordTrace tailWord_532176 prefixEnd_532176 30362453420801676961397 := by
  unfold tailWord_532176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9705026660012357634956191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12940035546683143513274921 9705026660012357634956191)
  ·
    refine ⟨14557539990018536452434287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9705026660012357634956191 14557539990018536452434287)
    ·
      refine ⟨21836309985027804678651431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14557539990018536452434287 21836309985027804678651431)
      ·
        refine ⟨32754464977541707017977147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21836309985027804678651431 32754464977541707017977147)
        ·
          refine ⟨49131697466312560526965721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32754464977541707017977147 49131697466312560526965721)
          ·
            refine ⟨36848773099734420395224291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49131697466312560526965721 36848773099734420395224291)
            ·
              refine ⟨55273159649601630592836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36848773099734420395224291 55273159649601630592836437)
              ·
                refine ⟨323866169821884554254901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 55273159649601630592836437 323866169821884554254901)
                ·
                  refine ⟨30362453420801676961397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323866169821884554254901 30362453420801676961397)
                  ·
                    rfl

theorem cell23_532176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 5].length) (baseStart_532176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532176 prefixEnd_532176 := by exact prefixLift 532176
  have htrace : WordTrace (prefixWord ++ tailWord_532176) baseStart_532176 baseEnd_532176 := by
    simpa [prefixWord, tailWord_532176, baseEnd_532176] using wordTrace_append hprefix tailTrace_532176
  have hstable : (prefixWord ++ tailWord_532176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532176).length < 2 ^ (prefixWord ++ tailWord_532176).sum := by decide
  have hdescent : baseEnd_532176 < baseStart_532176 := by decide
  rcases family_descends (prefixWord ++ tailWord_532176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532193 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 7]
def baseStart_532193 : Nat := 118140960795 + 532193 * 2 ^ 59
def prefixEnd_532193 : Nat := 4983230072969 + 3 ^ 40 * 532193 * 2
def baseEnd_532193 : Nat := 30363423328704614015555

theorem tailTrace_532193 : CollatzResearch.WordTrace tailWord_532193 prefixEnd_532193 30363423328704614015555 := by
  unfold tailWord_532193
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410673360963127173281233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12940448907308751448854155 19410673360963127173281233)
  ·
    refine ⟨14558005020722345379960925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19410673360963127173281233 14558005020722345379960925)
    ·
      refine ⟨5459251882770879517485347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14558005020722345379960925 5459251882770879517485347)
      ·
        refine ⟨8188877824156319276228021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459251882770879517485347 8188877824156319276228021)
        ·
          refine ⟨767707296014654932146377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8188877824156319276228021 767707296014654932146377)
          ·
            refine ⟨575780472010991199109783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767707296014654932146377 575780472010991199109783)
            ·
              refine ⟨863670708016486798664675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575780472010991199109783 863670708016486798664675)
              ·
                refine ⟨1295506062024730197997013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863670708016486798664675 1295506062024730197997013)
                ·
                  refine ⟨30363423328704614015555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1295506062024730197997013 30363423328704614015555)
                  ·
                    rfl

theorem cell23_532193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_532193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532193 prefixEnd_532193 := by exact prefixLift 532193
  have htrace : WordTrace (prefixWord ++ tailWord_532193) baseStart_532193 baseEnd_532193 := by
    simpa [prefixWord, tailWord_532193, baseEnd_532193] using wordTrace_append hprefix tailTrace_532193
  have hstable : (prefixWord ++ tailWord_532193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532193).length < 2 ^ (prefixWord ++ tailWord_532193).sum := by decide
  have hdescent : baseEnd_532193 < baseStart_532193 := by decide
  rcases family_descends (prefixWord ++ tailWord_532193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532206 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_532206 : Nat := 118140960795 + 532206 * 2 ^ 59
def prefixEnd_532206 : Nat := 4983230072969 + 3 ^ 40 * 532206 * 2
def baseEnd_532206 : Nat := 91092495068949991759145

theorem tailTrace_532206 : CollatzResearch.WordTrace tailWord_532206 prefixEnd_532206 91092495068949991759145 := by
  unfold tailWord_532206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426393438739503799188059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12940765006610686929002981 2426393438739503799188059)
  ·
    refine ⟨3639590158109255698782089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2426393438739503799188059 3639590158109255698782089)
    ·
      refine ⟨2729692618581941774086567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3639590158109255698782089 2729692618581941774086567)
      ·
        refine ⟨4094538927872912661129851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729692618581941774086567 4094538927872912661129851)
        ·
          refine ⟨6141808391809368991694777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4094538927872912661129851 6141808391809368991694777)
          ·
            refine ⟨4606356293857026743771083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6141808391809368991694777 4606356293857026743771083)
            ·
              refine ⟨6909534440785540115656625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606356293857026743771083 6909534440785540115656625)
              ·
                refine ⟨5182150830589155086742469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909534440785540115656625 5182150830589155086742469)
                ·
                  refine ⟨971653280735466578764213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5182150830589155086742469 971653280735466578764213)
                  ·
                    refine ⟨91092495068949991759145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 971653280735466578764213 91092495068949991759145)
                    ·
                      rfl

theorem cell23_532206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_532206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532206 prefixEnd_532206 := by exact prefixLift 532206
  have htrace : WordTrace (prefixWord ++ tailWord_532206) baseStart_532206 baseEnd_532206 := by
    simpa [prefixWord, tailWord_532206, baseEnd_532206] using wordTrace_append hprefix tailTrace_532206
  have hstable : (prefixWord ++ tailWord_532206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532206).length < 2 ^ (prefixWord ++ tailWord_532206).sum := by decide
  have hdescent : baseEnd_532206 < baseStart_532206 := by decide
  rcases family_descends (prefixWord ++ tailWord_532206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532229 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_532229 : Nat := 118140960795 + 532229 * 2 ^ 59
def prefixEnd_532229 : Nat := 4983230072969 + 3 ^ 40 * 532229 * 2
def baseEnd_532229 : Nat := 273289295261903385289829

theorem tailTrace_532229 : CollatzResearch.WordTrace tailWord_532229 prefixEnd_532229 273289295261903385289829 := by
  unfold tailWord_532229
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411986388832705321591741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941324259221803547727827 19411986388832705321591741)
  ·
    refine ⟨7279494895812264495596903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19411986388832705321591741 7279494895812264495596903)
    ·
      refine ⟨10919242343718396743395355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279494895812264495596903 10919242343718396743395355)
      ·
        refine ⟨16378863515577595115093033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919242343718396743395355 16378863515577595115093033)
        ·
          refine ⟨12284147636683196336319775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16378863515577595115093033 12284147636683196336319775)
          ·
            refine ⟨18426221455024794504479663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284147636683196336319775 18426221455024794504479663)
            ·
              refine ⟨27639332182537191756719495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18426221455024794504479663 27639332182537191756719495)
              ·
                refine ⟨41458998273805787635079243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27639332182537191756719495 41458998273805787635079243)
                ·
                  refine ⟨62188497410708681452618865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41458998273805787635079243 62188497410708681452618865)
                  ·
                    refine ⟨46641373058031511089464149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62188497410708681452618865 46641373058031511089464149)
                    ·
                      refine ⟨273289295261903385289829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 46641373058031511089464149 273289295261903385289829)
                      ·
                        rfl

theorem cell23_532229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_532229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532229 prefixEnd_532229 := by exact prefixLift 532229
  have htrace : WordTrace (prefixWord ++ tailWord_532229) baseStart_532229 baseEnd_532229 := by
    simpa [prefixWord, tailWord_532229, baseEnd_532229] using wordTrace_append hprefix tailTrace_532229
  have hstable : (prefixWord ++ tailWord_532229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532229).length < 2 ^ (prefixWord ++ tailWord_532229).sum := by decide
  have hdescent : baseEnd_532229 < baseStart_532229 := by decide
  rcases family_descends (prefixWord ++ tailWord_532229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532244 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 5]
def baseStart_532244 : Nat := 118140960795 + 532244 * 2 ^ 59
def prefixEnd_532244 : Nat := 4983230072969 + 3 ^ 40 * 532244 * 2
def baseEnd_532244 : Nat := 30366333052413425178029

theorem tailTrace_532244 : CollatzResearch.WordTrace tailWord_532244 prefixEnd_532244 30366333052413425178029 := by
  unfold tailWord_532244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706266741889181441693893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12941688989185575255591857 9706266741889181441693893)
  ·
    refine ⟨1819925014104221520317605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9706266741889181441693893 1819925014104221520317605)
    ·
      refine ⟨341235940144541535059551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1819925014104221520317605 341235940144541535059551)
      ·
        refine ⟨511853910216812302589327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341235940144541535059551 511853910216812302589327)
        ·
          refine ⟨767780865325218453883991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511853910216812302589327 767780865325218453883991)
          ·
            refine ⟨1151671297987827680825987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767780865325218453883991 1151671297987827680825987)
            ·
              refine ⟨1727506946981741521238981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151671297987827680825987 1727506946981741521238981)
              ·
                refine ⟨323907552559076535232309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1727506946981741521238981 323907552559076535232309)
                ·
                  refine ⟨30366333052413425178029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323907552559076535232309 30366333052413425178029)
                  ·
                    rfl

theorem cell23_532244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_532244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532244 prefixEnd_532244 := by exact prefixLift 532244
  have htrace : WordTrace (prefixWord ++ tailWord_532244) baseStart_532244 baseEnd_532244 := by
    simpa [prefixWord, tailWord_532244, baseEnd_532244] using wordTrace_append hprefix tailTrace_532244
  have hstable : (prefixWord ++ tailWord_532244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532244).length < 2 ^ (prefixWord ++ tailWord_532244).sum := by decide
  have hdescent : baseEnd_532244 < baseStart_532244 := by decide
  rcases family_descends (prefixWord ++ tailWord_532244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532249 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 12]
def baseStart_532249 : Nat := 118140960795 + 532249 * 2 ^ 59
def prefixEnd_532249 : Nat := 4983230072969 + 3 ^ 40 * 532249 * 2
def baseEnd_532249 : Nat := 30366618319443700782193

theorem tailTrace_532249 : CollatzResearch.WordTrace tailWord_532249 prefixEnd_532249 30366618319443700782193 := by
  unfold tailWord_532249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412715848760248737319801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12941810565840165824879867 19412715848760248737319801)
  ·
    refine ⟨14559536886570186552989851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19412715848760248737319801 14559536886570186552989851)
    ·
      refine ⟨21839305329855279829484777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14559536886570186552989851 21839305329855279829484777)
      ·
        refine ⟨16379478997391459872113583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21839305329855279829484777 16379478997391459872113583)
        ·
          refine ⟨24569218496087189808170375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16379478997391459872113583 24569218496087189808170375)
          ·
            refine ⟨36853827744130784712255563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24569218496087189808170375 36853827744130784712255563)
            ·
              refine ⟨55280741616196177068383345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36853827744130784712255563 55280741616196177068383345)
              ·
                refine ⟨41460556212147132801287509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55280741616196177068383345 41460556212147132801287509)
                ·
                  refine ⟨30366618319443700782193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 41460556212147132801287509 30366618319443700782193)
                  ·
                    rfl

theorem cell23_532249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_532249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532249 prefixEnd_532249 := by exact prefixLift 532249
  have htrace : WordTrace (prefixWord ++ tailWord_532249) baseStart_532249 baseEnd_532249 := by
    simpa [prefixWord, tailWord_532249, baseEnd_532249] using wordTrace_append hprefix tailTrace_532249
  have hstable : (prefixWord ++ tailWord_532249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532249).length < 2 ^ (prefixWord ++ tailWord_532249).sum := by decide
  have hdescent : baseEnd_532249 < baseStart_532249 := by decide
  rcases family_descends (prefixWord ++ tailWord_532249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532260 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_532260 : Nat := 118140960795 + 532260 * 2 ^ 59
def prefixEnd_532260 : Nat := 4983230072969 + 3 ^ 40 * 532260 * 2
def baseEnd_532260 : Nat := 273305213162192764002187

theorem tailTrace_532260 : CollatzResearch.WordTrace tailWord_532260 prefixEnd_532260 273305213162192764002187 := by
  unfold tailWord_532260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706558525860198807985117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12942078034480265077313489 9706558525860198807985117)
  ·
    refine ⟨3639959447197574552994419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9706558525860198807985117 3639959447197574552994419)
    ·
      refine ⟨5459939170796361829491629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3639959447197574552994419 5459939170796361829491629)
      ·
        refine ⟨2047477189048635686059361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5459939170796361829491629 2047477189048635686059361)
        ·
          refine ⟨1535607891786476764544521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047477189048635686059361 1535607891786476764544521)
          ·
            refine ⟨1151705918839857573408391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535607891786476764544521 1151705918839857573408391)
            ·
              refine ⟨1727558878259786360112587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151705918839857573408391 1727558878259786360112587)
              ·
                refine ⟨2591338317389679540168881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727558878259786360112587 2591338317389679540168881)
                ·
                  refine ⟨1943503738042259655126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591338317389679540168881 1943503738042259655126661)
                  ·
                    refine ⟨364406950882923685336249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943503738042259655126661 364406950882923685336249)
                    ·
                      refine ⟨273305213162192764002187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364406950882923685336249 273305213162192764002187)
                      ·
                        rfl

theorem cell23_532260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_532260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532260 prefixEnd_532260 := by exact prefixLift 532260
  have htrace : WordTrace (prefixWord ++ tailWord_532260) baseStart_532260 baseEnd_532260 := by
    simpa [prefixWord, tailWord_532260, baseEnd_532260] using wordTrace_append hprefix tailTrace_532260
  have hstable : (prefixWord ++ tailWord_532260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532260).length < 2 ^ (prefixWord ++ tailWord_532260).sum := by decide
  have hdescent : baseEnd_532260 < baseStart_532260 := by decide
  rcases family_descends (prefixWord ++ tailWord_532260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532277 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_532277 : Nat := 118140960795 + 532277 * 2 ^ 59
def prefixEnd_532277 : Nat := 4983230072969 + 3 ^ 40 * 532277 * 2
def baseEnd_532277 : Nat := 273313942333319197489609

theorem tailTrace_532277 : CollatzResearch.WordTrace tailWord_532277 prefixEnd_532277 273313942333319197489609 := by
  unfold tailWord_532277
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413737092658809519339085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12942491395105873012892723 19413737092658809519339085)
  ·
    refine ⟨7280151409747053569752157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19413737092658809519339085 7280151409747053569752157)
    ·
      refine ⟨2730056778655145088657059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7280151409747053569752157 2730056778655145088657059)
      ·
        refine ⟨4095085167982717632985589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730056778655145088657059 4095085167982717632985589)
        ·
          refine ⟨383914234498379778092399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4095085167982717632985589 383914234498379778092399)
          ·
            refine ⟨575871351747569667138599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383914234498379778092399 575871351747569667138599)
            ·
              refine ⟨863807027621354500707899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575871351747569667138599 863807027621354500707899)
              ·
                refine ⟨1295710541432031751061849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863807027621354500707899 1295710541432031751061849)
                ·
                  refine ⟨971782906074023813296387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295710541432031751061849 971782906074023813296387)
                  ·
                    refine ⟨1457674359111035719944581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 971782906074023813296387 1457674359111035719944581)
                    ·
                      refine ⟨273313942333319197489609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1457674359111035719944581 273313942333319197489609)
                      ·
                        rfl

theorem cell23_532277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_532277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532277 prefixEnd_532277 := by exact prefixLift 532277
  have htrace : WordTrace (prefixWord ++ tailWord_532277) baseStart_532277 baseEnd_532277 := by
    simpa [prefixWord, tailWord_532277, baseEnd_532277] using wordTrace_append hprefix tailTrace_532277
  have hstable : (prefixWord ++ tailWord_532277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532277).length < 2 ^ (prefixWord ++ tailWord_532277).sum := by decide
  have hdescent : baseEnd_532277 < baseStart_532277 := by decide
  rcases family_descends (prefixWord ++ tailWord_532277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532280 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_532280 : Nat := 118140960795 + 532280 * 2 ^ 59
def prefixEnd_532280 : Nat := 4983230072969 + 3 ^ 40 * 532280 * 2
def baseEnd_532280 : Nat := 273315482775282685752095

theorem tailTrace_532280 : CollatzResearch.WordTrace tailWord_532280 prefixEnd_532280 273315482775282685752095 := by
  unfold tailWord_532280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706923255823970515849147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12942564341098627354465529 9706923255823970515849147)
  ·
    refine ⟨14560384883735955773773721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9706923255823970515849147 14560384883735955773773721)
    ·
      refine ⟨10920288662801966830330291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14560384883735955773773721 10920288662801966830330291)
      ·
        refine ⟨16380432994202950245495437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10920288662801966830330291 16380432994202950245495437)
        ·
          refine ⟨6142662372826106342060789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16380432994202950245495437 6142662372826106342060789)
          ·
            refine ⟨575874597452447469568199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6142662372826106342060789 575874597452447469568199)
            ·
              refine ⟨863811896178671204352299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575874597452447469568199 863811896178671204352299)
              ·
                refine ⟨1295717844268006806528449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863811896178671204352299 1295717844268006806528449)
                ·
                  refine ⟨971788383201005104896337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295717844268006806528449 971788383201005104896337)
                  ·
                    refine ⟨728841287400753828672253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 971788383201005104896337 728841287400753828672253)
                    ·
                      refine ⟨273315482775282685752095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728841287400753828672253 273315482775282685752095)
                      ·
                        rfl

theorem cell23_532280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_532280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532280 prefixEnd_532280 := by exact prefixLift 532280
  have htrace : WordTrace (prefixWord ++ tailWord_532280) baseStart_532280 baseEnd_532280 := by
    simpa [prefixWord, tailWord_532280, baseEnd_532280] using wordTrace_append hprefix tailTrace_532280
  have hstable : (prefixWord ++ tailWord_532280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532280).length < 2 ^ (prefixWord ++ tailWord_532280).sum := by decide
  have hdescent : baseEnd_532280 < baseStart_532280 := by decide
  rcases family_descends (prefixWord ++ tailWord_532280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532287 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 1, 4]
def baseStart_532287 : Nat := 118140960795 + 532287 * 2 ^ 59
def prefixEnd_532287 : Nat := 4983230072969 + 3 ^ 40 * 532287 * 2
def baseEnd_532287 : Nat := 91106359046621386121521

theorem tailTrace_532287 : CollatzResearch.WordTrace tailWord_532287 prefixEnd_532287 91106359046621386121521 := by
  unfold tailWord_532287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414101822622581227203115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12942734548415054151468743 19414101822622581227203115)
  ·
    refine ⟨29121152733933871840804673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19414101822622581227203115 29121152733933871840804673)
    ·
      refine ⟨21840864550450403880603505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29121152733933871840804673 21840864550450403880603505)
      ·
        refine ⟨16380648412837802910452629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21840864550450403880603505 16380648412837802910452629)
        ·
          refine ⟨767842894351772011427467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16380648412837802910452629 767842894351772011427467)
          ·
            refine ⟨1151764341527658017141201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767842894351772011427467 1151764341527658017141201)
            ·
              refine ⟨863823256145743512855901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151764341527658017141201 863823256145743512855901)
              ·
                refine ⟨323933721054653817320963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863823256145743512855901 323933721054653817320963)
                ·
                  refine ⟨485900581581980725981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323933721054653817320963 485900581581980725981445)
                  ·
                    refine ⟨91106359046621386121521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 485900581581980725981445 91106359046621386121521)
                    ·
                      rfl

theorem cell23_532287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_532287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532287 prefixEnd_532287 := by exact prefixLift 532287
  have htrace : WordTrace (prefixWord ++ tailWord_532287) baseStart_532287 baseEnd_532287 := by
    simpa [prefixWord, tailWord_532287, baseEnd_532287] using wordTrace_append hprefix tailTrace_532287
  have hstable : (prefixWord ++ tailWord_532287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532287).length < 2 ^ (prefixWord ++ tailWord_532287).sum := by decide
  have hdescent : baseEnd_532287 < baseStart_532287 := by decide
  rcases family_descends (prefixWord ++ tailWord_532287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532293 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_532293 : Nat := 118140960795 + 532293 * 2 ^ 59
def prefixEnd_532293 : Nat := 4983230072969 + 3 ^ 40 * 532293 * 2
def baseEnd_532293 : Nat := 273322158023791134889535

theorem tailTrace_532293 : CollatzResearch.WordTrace tailWord_532293 prefixEnd_532293 273322158023791134889535 := by
  unfold tailWord_532293
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414320660600844251921533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12942880440400562834614355 19414320660600844251921533)
  ·
    refine ⟨7280370247725316594470575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19414320660600844251921533 7280370247725316594470575)
    ·
      refine ⟨10920555371587974891705863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280370247725316594470575 10920555371587974891705863)
      ·
        refine ⟨16380833057381962337558795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10920555371587974891705863 16380833057381962337558795)
        ·
          refine ⟨24571249586072943506338193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16380833057381962337558795 24571249586072943506338193)
          ·
            refine ⟨18428437189554707629753645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24571249586072943506338193 18428437189554707629753645)
            ·
              refine ⟨6910663946083015361157617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18428437189554707629753645 6910663946083015361157617)
              ·
                refine ⟨5182997959562261520868213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6910663946083015361157617 5182997959562261520868213)
                ·
                  refine ⟨485906058708962017581395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5182997959562261520868213 485906058708962017581395)
                  ·
                    refine ⟨728859088063443026372093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 485906058708962017581395 728859088063443026372093)
                    ·
                      refine ⟨273322158023791134889535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 728859088063443026372093 273322158023791134889535)
                      ·
                        rfl

theorem cell23_532293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_532293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532293 prefixEnd_532293 := by exact prefixLift 532293
  have htrace : WordTrace (prefixWord ++ tailWord_532293) baseStart_532293 baseEnd_532293 := by
    simpa [prefixWord, tailWord_532293, baseEnd_532293] using wordTrace_append hprefix tailTrace_532293
  have hstable : (prefixWord ++ tailWord_532293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532293).length < 2 ^ (prefixWord ++ tailWord_532293).sum := by decide
  have hdescent : baseEnd_532293 < baseStart_532293 := by decide
  rcases family_descends (prefixWord ++ tailWord_532293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532300 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 6]
def baseStart_532300 : Nat := 118140960795 + 532300 * 2 ^ 59
def prefixEnd_532300 : Nat := 4983230072969 + 3 ^ 40 * 532300 * 2
def baseEnd_532300 : Nat := 30369528043152511944667

theorem tailTrace_532300 : CollatzResearch.WordTrace tailWord_532300 prefixEnd_532300 30369528043152511944667 := by
  unfold tailWord_532300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707287985787742223713177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12943050647716989631617569 9707287985787742223713177)
  ·
    refine ⟨7280465989340806667784883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9707287985787742223713177 7280465989340806667784883)
    ·
      refine ⟨10920698984011210001677325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280465989340806667784883 10920698984011210001677325)
      ·
        refine ⟨4095262119004203750628997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10920698984011210001677325 4095262119004203750628997)
        ·
          refine ⟨767861647313288203242937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4095262119004203750628997 767861647313288203242937)
          ·
            refine ⟨575896235484966152432203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767861647313288203242937 575896235484966152432203)
            ·
              refine ⟨863844353227449228648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575896235484966152432203 863844353227449228648305)
              ·
                refine ⟨647883264920586921486229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863844353227449228648305 647883264920586921486229)
                ·
                  refine ⟨30369528043152511944667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 647883264920586921486229 30369528043152511944667)
                  ·
                    rfl

theorem cell23_532300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_532300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532300 prefixEnd_532300 := by exact prefixLift 532300
  have htrace : WordTrace (prefixWord ++ tailWord_532300) baseStart_532300 baseEnd_532300 := by
    simpa [prefixWord, tailWord_532300, baseEnd_532300] using wordTrace_append hprefix tailTrace_532300
  have hstable : (prefixWord ++ tailWord_532300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532300).length < 2 ^ (prefixWord ++ tailWord_532300).sum := by decide
  have hdescent : baseEnd_532300 < baseStart_532300 := by decide
  rcases family_descends (prefixWord ++ tailWord_532300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532333 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_532333 : Nat := 118140960795 + 532333 * 2 ^ 59
def prefixEnd_532333 : Nat := 4983230072969 + 3 ^ 40 * 532333 * 2
def baseEnd_532333 : Nat := 273342697249970978389351

theorem tailTrace_532333 : CollatzResearch.WordTrace tailWord_532333 prefixEnd_532333 273342697249970978389351 := by
  unfold tailWord_532333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19415779580455931083377653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12943853053637287388918435 19415779580455931083377653)
  ·
    refine ⟨1820229335667743539066655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19415779580455931083377653 1820229335667743539066655)
    ·
      refine ⟨2730344003501615308599983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820229335667743539066655 2730344003501615308599983)
      ·
        refine ⟨4095516005252422962899975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730344003501615308599983 4095516005252422962899975)
        ·
          refine ⟨6143274007878634444349963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095516005252422962899975 6143274007878634444349963)
          ·
            refine ⟨9214911011817951666524945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143274007878634444349963 9214911011817951666524945)
            ·
              refine ⟨6911183258863463749893709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9214911011817951666524945 6911183258863463749893709)
              ·
                refine ⟨2591693722073798906210141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6911183258863463749893709 2591693722073798906210141)
                ·
                  refine ⟨971885145777674589828803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2591693722073798906210141 971885145777674589828803)
                  ·
                    refine ⟨1457827718666511884743205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 971885145777674589828803 1457827718666511884743205)
                    ·
                      refine ⟨273342697249970978389351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1457827718666511884743205 273342697249970978389351)
                      ·
                        rfl

theorem cell23_532333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_532333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532333 prefixEnd_532333 := by exact prefixLift 532333
  have htrace : WordTrace (prefixWord ++ tailWord_532333) baseStart_532333 baseEnd_532333 := by
    simpa [prefixWord, tailWord_532333, baseEnd_532333] using wordTrace_append hprefix tailTrace_532333
  have hstable : (prefixWord ++ tailWord_532333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532333).length < 2 ^ (prefixWord ++ tailWord_532333).sum := by decide
  have hdescent : baseEnd_532333 < baseStart_532333 := by decide
  rcases family_descends (prefixWord ++ tailWord_532333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532336 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_532336 : Nat := 118140960795 + 532336 * 2 ^ 59
def prefixEnd_532336 : Nat := 4983230072969 + 3 ^ 40 * 532336 * 2
def baseEnd_532336 : Nat := 273344237691934466651837

theorem tailTrace_532336 : CollatzResearch.WordTrace tailWord_532336 prefixEnd_532336 273344237691934466651837 := by
  unfold tailWord_532336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707944499722531297868431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12943925999630041730491241 9707944499722531297868431)
  ·
    refine ⟨14561916749583796946802647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9707944499722531297868431 14561916749583796946802647)
    ·
      refine ⟨21842875124375695420203971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14561916749583796946802647 21842875124375695420203971)
      ·
        refine ⟨32764312686563543130305957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21842875124375695420203971 32764312686563543130305957)
        ·
          refine ⟨6143308628730664336932367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32764312686563543130305957 6143308628730664336932367)
          ·
            refine ⟨9214962943095996505398551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143308628730664336932367 9214962943095996505398551)
            ·
              refine ⟨13822444414643994758097827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9214962943095996505398551 13822444414643994758097827)
              ·
                refine ⟨20733666621965992137146741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13822444414643994758097827 20733666621965992137146741)
                ·
                  refine ⟨1943781245809311762857507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20733666621965992137146741 1943781245809311762857507)
                  ·
                    refine ⟨2915671868713967644286261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943781245809311762857507 2915671868713967644286261)
                    ·
                      refine ⟨273344237691934466651837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2915671868713967644286261 273344237691934466651837)
                      ·
                        rfl

theorem cell23_532336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_532336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532336 prefixEnd_532336 := by exact prefixLift 532336
  have htrace : WordTrace (prefixWord ++ tailWord_532336) baseStart_532336 baseEnd_532336 := by
    simpa [prefixWord, tailWord_532336, baseEnd_532336] using wordTrace_append hprefix tailTrace_532336
  have hstable : (prefixWord ++ tailWord_532336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532336).length < 2 ^ (prefixWord ++ tailWord_532336).sum := by decide
  have hdescent : baseEnd_532336 < baseStart_532336 := by decide
  rcases family_descends (prefixWord ++ tailWord_532336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532356 : List Nat := [2, 3, 2, 1, 1, 1, 13]
def baseStart_532356 : Nat := 118140960795 + 532356 * 2 ^ 59
def prefixEnd_532356 : Nat := 4983230072969 + 3 ^ 40 * 532356 * 2
def baseEnd_532356 : Nat := 3374747003765733190145

theorem tailTrace_532356 : CollatzResearch.WordTrace tailWord_532356 prefixEnd_532356 3374747003765733190145 := by
  unfold tailWord_532356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708309229686303005732461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12944412306248404007643281 9708309229686303005732461)
  ·
    refine ⟨3640615961132363627149673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9708309229686303005732461 3640615961132363627149673)
    ·
      refine ⟨2730461970849272720362255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640615961132363627149673 2730461970849272720362255)
      ·
        refine ⟨4095692956273909080543383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730461970849272720362255 4095692956273909080543383)
        ·
          refine ⟨6143539434410863620815075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095692956273909080543383 6143539434410863620815075)
          ·
            refine ⟨9215309151616295431222613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143539434410863620815075 9215309151616295431222613)
            ·
              refine ⟨3374747003765733190145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 9215309151616295431222613 3374747003765733190145)
              ·
                rfl

theorem cell23_532356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 13].length) (baseStart_532356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532356 prefixEnd_532356 := by exact prefixLift 532356
  have htrace : WordTrace (prefixWord ++ tailWord_532356) baseStart_532356 baseEnd_532356 := by
    simpa [prefixWord, tailWord_532356, baseEnd_532356] using wordTrace_append hprefix tailTrace_532356
  have hstable : (prefixWord ++ tailWord_532356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532356).length < 2 ^ (prefixWord ++ tailWord_532356).sum := by decide
  have hdescent : baseEnd_532356 < baseStart_532356 := by decide
  rcases family_descends (prefixWord ++ tailWord_532356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532370 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_532370 : Nat := 118140960795 + 532370 * 2 ^ 59
def prefixEnd_532370 : Nat := 4983230072969 + 3 ^ 40 * 532370 * 2
def baseEnd_532370 : Nat := 273361696034187333626681

theorem tailTrace_532370 : CollatzResearch.WordTrace tailWord_532370 prefixEnd_532370 273361696034187333626681 := by
  unfold tailWord_532370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854282270330471600618641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12944752720881257601649709 4854282270330471600618641)
  ·
    refine ⟨3640711702747853700463981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4854282270330471600618641 3640711702747853700463981)
    ·
      refine ⟨1365266888530445137673993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3640711702747853700463981 1365266888530445137673993)
      ·
        refine ⟨1023950166397833853255495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365266888530445137673993 1023950166397833853255495)
        ·
          refine ⟨1535925249596750779883243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023950166397833853255495 1535925249596750779883243)
          ·
            refine ⟨2303887874395126169824865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535925249596750779883243 2303887874395126169824865)
            ·
              refine ⟨1727915905796344627368649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303887874395126169824865 1727915905796344627368649)
              ·
                refine ⟨1295936929347258470526487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727915905796344627368649 1295936929347258470526487)
                ·
                  refine ⟨1943905394020887705789731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295936929347258470526487 1943905394020887705789731)
                  ·
                    refine ⟨2915858091031331558684597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943905394020887705789731 2915858091031331558684597)
                    ·
                      refine ⟨273361696034187333626681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2915858091031331558684597 273361696034187333626681)
                      ·
                        rfl

theorem cell23_532370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_532370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532370 prefixEnd_532370 := by exact prefixLift 532370
  have htrace : WordTrace (prefixWord ++ tailWord_532370) baseStart_532370 baseEnd_532370 := by
    simpa [prefixWord, tailWord_532370, baseEnd_532370] using wordTrace_append hprefix tailTrace_532370
  have hstable : (prefixWord ++ tailWord_532370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532370).length < 2 ^ (prefixWord ++ tailWord_532370).sum := by decide
  have hdescent : baseEnd_532370 < baseStart_532370 := by decide
  rcases family_descends (prefixWord ++ tailWord_532370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532404 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_532404 : Nat := 118140960795 + 532404 * 2 ^ 59
def prefixEnd_532404 : Nat := 4983230072969 + 3 ^ 40 * 532404 * 2
def baseEnd_532404 : Nat := 273379154376440200601525

theorem tailTrace_532404 : CollatzResearch.WordTrace tailWord_532404 prefixEnd_532404 273379154376440200601525 := by
  unfold tailWord_532404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709184581599355104606133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12945579442132473472808177 9709184581599355104606133)
  ·
    refine ⟨910236054524939541056825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9709184581599355104606133 910236054524939541056825)
    ·
      refine ⟨682677040893704655792619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910236054524939541056825 682677040893704655792619)
      ·
        refine ⟨1024015561340556983688929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682677040893704655792619 1024015561340556983688929)
        ·
          refine ⟨768011671005417737766697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024015561340556983688929 768011671005417737766697)
          ·
            refine ⟨576008753254063303325023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768011671005417737766697 576008753254063303325023)
            ·
              refine ⟨864013129881094954987535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576008753254063303325023 864013129881094954987535)
              ·
                refine ⟨1296019694821642432481303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864013129881094954987535 1296019694821642432481303)
                ·
                  refine ⟨1944029542232463648721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296019694821642432481303 1944029542232463648721955)
                  ·
                    refine ⟨2916044313348695473082933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944029542232463648721955 2916044313348695473082933)
                    ·
                      refine ⟨273379154376440200601525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2916044313348695473082933 273379154376440200601525)
                      ·
                        rfl

theorem cell23_532404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_532404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532404 prefixEnd_532404 := by exact prefixLift 532404
  have htrace : WordTrace (prefixWord ++ tailWord_532404) baseStart_532404 baseEnd_532404 := by
    simpa [prefixWord, tailWord_532404, baseEnd_532404] using wordTrace_append hprefix tailTrace_532404
  have hstable : (prefixWord ++ tailWord_532404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532404).length < 2 ^ (prefixWord ++ tailWord_532404).sum := by decide
  have hdescent : baseEnd_532404 < baseStart_532404 := by decide
  rcases family_descends (prefixWord ++ tailWord_532404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532461 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_532461 : Nat := 118140960795 + 532461 * 2 ^ 59
def prefixEnd_532461 : Nat := 4983230072969 + 3 ^ 40 * 532461 * 2
def baseEnd_532461 : Nat := 273408422773746477588763

theorem tailTrace_532461 : CollatzResearch.WordTrace tailWord_532461 prefixEnd_532461 273408422773746477588763 := by
  unfold tailWord_532461
  simp only [CollatzResearch.WordTrace]
  refine ⟨19420448123992208944037237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12946965415994805962691491 19420448123992208944037237)
  ·
    refine ⟨1820667011624269588503491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19420448123992208944037237 1820667011624269588503491)
    ·
      refine ⟨2731000517436404382755237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820667011624269588503491 2731000517436404382755237)
      ·
        refine ⟨512062597019325821766607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2731000517436404382755237 512062597019325821766607)
        ·
          refine ⟨768093895528988732649911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512062597019325821766607 768093895528988732649911)
          ·
            refine ⟨1152140843293483098974867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768093895528988732649911 1152140843293483098974867)
            ·
              refine ⟨1728211264940224648462301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152140843293483098974867 1728211264940224648462301)
              ·
                refine ⟨648079224352584243173363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728211264940224648462301 648079224352584243173363)
                ·
                  refine ⟨972118836528876364760045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648079224352584243173363 972118836528876364760045)
                  ·
                    refine ⟨364544563698328636785017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972118836528876364760045 364544563698328636785017)
                    ·
                      refine ⟨273408422773746477588763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364544563698328636785017 273408422773746477588763)
                      ·
                        rfl

theorem cell23_532461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_532461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532461 prefixEnd_532461 := by exact prefixLift 532461
  have htrace : WordTrace (prefixWord ++ tailWord_532461) baseStart_532461 baseEnd_532461 := by
    simpa [prefixWord, tailWord_532461, baseEnd_532461] using wordTrace_append hprefix tailTrace_532461
  have hstable : (prefixWord ++ tailWord_532461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532461).length < 2 ^ (prefixWord ++ tailWord_532461).sum := by decide
  have hdescent : baseEnd_532461 < baseStart_532461 := by decide
  rcases family_descends (prefixWord ++ tailWord_532461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532530 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_532530 : Nat := 118140960795 + 532530 * 2 ^ 59
def prefixEnd_532530 : Nat := 4983230072969 + 3 ^ 40 * 532530 * 2
def baseEnd_532530 : Nat := 273443852938906707625945

theorem tailTrace_532530 : CollatzResearch.WordTrace tailWord_532530 prefixEnd_532530 273443852938906707625945 := by
  unfold tailWord_532530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855741190185558432074761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12948643173828155818866029 4855741190185558432074761)
  ·
    refine ⟨3641805892639168824056071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4855741190185558432074761 3641805892639168824056071)
    ·
      refine ⟨5462708838958753236084107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3641805892639168824056071 5462708838958753236084107)
      ·
        refine ⟨8194063258438129854126161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5462708838958753236084107 8194063258438129854126161)
        ·
          refine ⟨6145547443828597390594621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8194063258438129854126161 6145547443828597390594621)
          ·
            refine ⟨2304580291435724021472983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6145547443828597390594621 2304580291435724021472983)
            ·
              refine ⟨3456870437153586032209475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304580291435724021472983 3456870437153586032209475)
              ·
                refine ⟨5185305655730379048314213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456870437153586032209475 5185305655730379048314213)
                ·
                  refine ⟨972244810449446071558915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5185305655730379048314213 972244810449446071558915)
                  ·
                    refine ⟨1458367215674169107338373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 972244810449446071558915 1458367215674169107338373)
                    ·
                      refine ⟨273443852938906707625945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1458367215674169107338373 273443852938906707625945)
                      ·
                        rfl

theorem cell23_532530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_532530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532530 prefixEnd_532530 := by exact prefixLift 532530
  have htrace : WordTrace (prefixWord ++ tailWord_532530) baseStart_532530 baseEnd_532530 := by
    simpa [prefixWord, tailWord_532530, baseEnd_532530] using wordTrace_append hprefix tailTrace_532530
  have hstable : (prefixWord ++ tailWord_532530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532530).length < 2 ^ (prefixWord ++ tailWord_532530).sum := by decide
  have hdescent : baseEnd_532530 < baseStart_532530 := by decide
  rcases family_descends (prefixWord ++ tailWord_532530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532543 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_532543 : Nat := 118140960795 + 532543 * 2 ^ 59
def prefixEnd_532543 : Nat := 4983230072969 + 3 ^ 40 * 532543 * 2
def baseEnd_532543 : Nat := 273450528187415156763385

theorem tailTrace_532543 : CollatzResearch.WordTrace tailWord_532543 prefixEnd_532543 273450528187415156763385 := by
  unfold tailWord_532543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19423438909695136948522283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12948959273130091299014855 19423438909695136948522283)
  ·
    refine ⟨29135158364542705422783425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19423438909695136948522283 29135158364542705422783425)
    ·
      refine ⟨21851368773407029067087569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29135158364542705422783425 21851368773407029067087569)
      ·
        refine ⟨16388526580055271800315677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21851368773407029067087569 16388526580055271800315677)
        ·
          refine ⟨6145697467520726925118379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16388526580055271800315677 6145697467520726925118379)
          ·
            refine ⟨9218546201281090387677569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6145697467520726925118379 9218546201281090387677569)
            ·
              refine ⟨6913909650960817790758177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9218546201281090387677569 6913909650960817790758177)
              ·
                refine ⟨5185432238220613343068633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6913909650960817790758177 5185432238220613343068633)
                ·
                  refine ⟨3889074178665460007301475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5185432238220613343068633 3889074178665460007301475)
                  ·
                    refine ⟨5833611267998190010952213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3889074178665460007301475 5833611267998190010952213)
                    ·
                      refine ⟨273450528187415156763385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5833611267998190010952213 273450528187415156763385)
                      ·
                        rfl

theorem cell23_532543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_532543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532543 prefixEnd_532543 := by exact prefixLift 532543
  have htrace : WordTrace (prefixWord ++ tailWord_532543) baseStart_532543 baseEnd_532543 := by
    simpa [prefixWord, tailWord_532543, baseEnd_532543] using wordTrace_append hprefix tailTrace_532543
  have hstable : (prefixWord ++ tailWord_532543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532543).length < 2 ^ (prefixWord ++ tailWord_532543).sum := by decide
  have hdescent : baseEnd_532543 < baseStart_532543 := by decide
  rcases family_descends (prefixWord ++ tailWord_532543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532557 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_532557 : Nat := 118140960795 + 532557 * 2 ^ 59
def prefixEnd_532557 : Nat := 4983230072969 + 3 ^ 40 * 532557 * 2
def baseEnd_532557 : Nat := 91152572305526033996107

theorem tailTrace_532557 : CollatzResearch.WordTrace tailWord_532557 prefixEnd_532557 91152572305526033996107 := by
  unfold tailWord_532557
  simp only [CollatzResearch.WordTrace]
  refine ⟨19423949531644417339531925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12949299687762944893021283 19423949531644417339531925)
  ·
    refine ⟨910497634295832062790559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19423949531644417339531925 910497634295832062790559)
    ·
      refine ⟨1365746451443748094185839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910497634295832062790559 1365746451443748094185839)
      ·
        refine ⟨2048619677165622141278759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365746451443748094185839 2048619677165622141278759)
        ·
          refine ⟨3072929515748433211918139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048619677165622141278759 3072929515748433211918139)
          ·
            refine ⟨4609394273622649817877209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072929515748433211918139 4609394273622649817877209)
            ·
              refine ⟨3457045705216987363407907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4609394273622649817877209 3457045705216987363407907)
              ·
                refine ⟨5185568557825481045111861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457045705216987363407907 5185568557825481045111861)
                ·
                  refine ⟨486147052296138847979237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5185568557825481045111861 486147052296138847979237)
                  ·
                    refine ⟨91152572305526033996107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486147052296138847979237 91152572305526033996107)
                    ·
                      rfl

theorem cell23_532557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_532557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532557 prefixEnd_532557 := by exact prefixLift 532557
  have htrace : WordTrace (prefixWord ++ tailWord_532557) baseStart_532557 baseEnd_532557 := by
    simpa [prefixWord, tailWord_532557, baseEnd_532557] using wordTrace_append hprefix tailTrace_532557
  have hstable : (prefixWord ++ tailWord_532557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532557).length < 2 ^ (prefixWord ++ tailWord_532557).sum := by decide
  have hdescent : baseEnd_532557 < baseStart_532557 := by decide
  rcases family_descends (prefixWord ++ tailWord_532557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532590 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_532590 : Nat := 118140960795 + 532590 * 2 ^ 59
def prefixEnd_532590 : Nat := 4983230072969 + 3 ^ 40 * 532590 * 2
def baseEnd_532590 : Nat := 273474661778176472875669

theorem tailTrace_532590 : CollatzResearch.WordTrace tailWord_532590 prefixEnd_532590 273474661778176472875669 := by
  unfold tailWord_532590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428144142565607996935403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12950102093683242650322149 2428144142565607996935403)
  ·
    refine ⟨3642216213848411995403105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2428144142565607996935403 3642216213848411995403105)
    ·
      refine ⟨2731662160386308996552329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3642216213848411995403105 2731662160386308996552329)
      ·
        refine ⟨2048746620289731747414247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2731662160386308996552329 2048746620289731747414247)
        ·
          refine ⟨3073119930434597621121371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048746620289731747414247 3073119930434597621121371)
          ·
            refine ⟨4609679895651896431682057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073119930434597621121371 4609679895651896431682057)
            ·
              refine ⟨3457259921738922323761543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4609679895651896431682057 3457259921738922323761543)
              ·
                refine ⟨5185889882608383485642315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457259921738922323761543 5185889882608383485642315)
                ·
                  refine ⟨7778834823912575228463473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185889882608383485642315 7778834823912575228463473)
                  ·
                    refine ⟨5834126117934431421347605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7778834823912575228463473 5834126117934431421347605)
                    ·
                      refine ⟨273474661778176472875669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5834126117934431421347605 273474661778176472875669)
                      ·
                        rfl

theorem cell23_532590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_532590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532590 prefixEnd_532590 := by exact prefixLift 532590
  have htrace : WordTrace (prefixWord ++ tailWord_532590) baseStart_532590 baseEnd_532590 := by
    simpa [prefixWord, tailWord_532590, baseEnd_532590] using wordTrace_append hprefix tailTrace_532590
  have hstable : (prefixWord ++ tailWord_532590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532590).length < 2 ^ (prefixWord ++ tailWord_532590).sum := by decide
  have hdescent : baseEnd_532590 < baseStart_532590 := by decide
  rcases family_descends (prefixWord ++ tailWord_532590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532591 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 1, 4]
def baseStart_532591 : Nat := 118140960795 + 532591 * 2 ^ 59
def prefixEnd_532591 : Nat := 4983230072969 + 3 ^ 40 * 532591 * 2
def baseEnd_532591 : Nat := 91158391752943656321055

theorem tailTrace_532591 : CollatzResearch.WordTrace tailWord_532591 prefixEnd_532591 91158391752943656321055 := by
  unfold tailWord_532591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19425189613521241146269627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12950126409014160764179751 19425189613521241146269627)
  ·
    refine ⟨29137784420281861719404441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19425189613521241146269627 29137784420281861719404441)
    ·
      refine ⟨21853338315211396289553331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29137784420281861719404441 21853338315211396289553331)
      ·
        refine ⟨32780007472817094434329997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21853338315211396289553331 32780007472817094434329997)
        ·
          refine ⟨12292502802306410412873749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32780007472817094434329997 12292502802306410412873749)
          ·
            refine ⟨576211068858112988103457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12292502802306410412873749 576211068858112988103457)
            ·
              refine ⟨432158301643584741077593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576211068858112988103457 432158301643584741077593)
              ·
                refine ⟨324118726232688555808195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432158301643584741077593 324118726232688555808195)
                ·
                  refine ⟨486178089349032833712293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324118726232688555808195 486178089349032833712293)
                  ·
                    refine ⟨91158391752943656321055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486178089349032833712293 91158391752943656321055)
                    ·
                      rfl

theorem cell23_532591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_532591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532591 prefixEnd_532591 := by exact prefixLift 532591
  have htrace : WordTrace (prefixWord ++ tailWord_532591) baseStart_532591 baseEnd_532591 := by
    simpa [prefixWord, tailWord_532591, baseEnd_532591] using wordTrace_append hprefix tailTrace_532591
  have hstable : (prefixWord ++ tailWord_532591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532591).length < 2 ^ (prefixWord ++ tailWord_532591).sum := by decide
  have hdescent : baseEnd_532591 < baseStart_532591 := by decide
  rcases family_descends (prefixWord ++ tailWord_532591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532634 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_532634 : Nat := 118140960795 + 532634 * 2 ^ 59
def prefixEnd_532634 : Nat := 4983230072969 + 3 ^ 40 * 532634 * 2
def baseEnd_532634 : Nat := 91165751642324766908489

theorem tailTrace_532634 : CollatzResearch.WordTrace tailWord_532634 prefixEnd_532634 91165751642324766908489 := by
  unfold tailWord_532634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4856689488091364872521239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12951171968243639660056637 4856689488091364872521239)
  ·
    refine ⟨7285034232137047308781859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4856689488091364872521239 7285034232137047308781859)
    ·
      refine ⟨10927551348205570963172789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285034232137047308781859 10927551348205570963172789)
      ·
        refine ⟨1024457938894272277797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10927551348205570963172789 1024457938894272277797449)
        ·
          refine ⟨768343454170704208348087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024457938894272277797449 768343454170704208348087)
          ·
            refine ⟨1152515181256056312522131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768343454170704208348087 1152515181256056312522131)
            ·
              refine ⟨1728772771884084468783197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152515181256056312522131 1728772771884084468783197)
              ·
                refine ⟨648289789456531675793699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728772771884084468783197 648289789456531675793699)
                ·
                  refine ⟨972434684184797513690549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648289789456531675793699 972434684184797513690549)
                  ·
                    refine ⟨91165751642324766908489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 972434684184797513690549 91165751642324766908489)
                    ·
                      rfl

theorem cell23_532634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_532634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532634 prefixEnd_532634 := by exact prefixLift 532634
  have htrace : WordTrace (prefixWord ++ tailWord_532634) baseStart_532634 baseEnd_532634 := by
    simpa [prefixWord, tailWord_532634, baseEnd_532634] using wordTrace_append hprefix tailTrace_532634
  have hstable : (prefixWord ++ tailWord_532634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532634).length < 2 ^ (prefixWord ++ tailWord_532634).sum := by decide
  have hdescent : baseEnd_532634 < baseStart_532634 := by decide
  rcases family_descends (prefixWord ++ tailWord_532634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532664 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_532664 : Nat := 118140960795 + 532664 * 2 ^ 59
def prefixEnd_532664 : Nat := 4983230072969 + 3 ^ 40 * 532664 * 2
def baseEnd_532664 : Nat := 91170886448869727783443

theorem tailTrace_532664 : CollatzResearch.WordTrace tailWord_532664 prefixEnd_532664 91170886448869727783443 := by
  unfold tailWord_532664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9713926071128387306838523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12951901428171183075784697 9713926071128387306838523)
  ·
    refine ⟨14570889106692580960257785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9713926071128387306838523 14570889106692580960257785)
    ·
      refine ⟨10928166830019435720193339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14570889106692580960257785 10928166830019435720193339)
      ·
        refine ⟨16392250245029153580290009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10928166830019435720193339 16392250245029153580290009)
        ·
          refine ⟨12294187683771865185217507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16392250245029153580290009 12294187683771865185217507)
          ·
            refine ⟨18441281525657797777826261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12294187683771865185217507 18441281525657797777826261)
            ·
              refine ⟨432217535757604635417803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18441281525657797777826261 432217535757604635417803)
              ·
                refine ⟨648326303636406953126705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432217535757604635417803 648326303636406953126705)
                ·
                  refine ⟨486244727727305214845029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648326303636406953126705 486244727727305214845029)
                  ·
                    refine ⟨91170886448869727783443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486244727727305214845029 91170886448869727783443)
                    ·
                      rfl

theorem cell23_532664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_532664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532664 prefixEnd_532664 := by exact prefixLift 532664
  have htrace : WordTrace (prefixWord ++ tailWord_532664) baseStart_532664 baseEnd_532664 := by
    simpa [prefixWord, tailWord_532664, baseEnd_532664] using wordTrace_append hprefix tailTrace_532664
  have hstable : (prefixWord ++ tailWord_532664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532664).length < 2 ^ (prefixWord ++ tailWord_532664).sum := by decide
  have hdescent : baseEnd_532664 < baseStart_532664 := by decide
  rcases family_descends (prefixWord ++ tailWord_532664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532687 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_532687 : Nat := 118140960795 + 532687 * 2 ^ 59
def prefixEnd_532687 : Nat := 4983230072969 + 3 ^ 40 * 532687 * 2
def baseEnd_532687 : Nat := 273524469401662593362723

theorem tailTrace_532687 : CollatzResearch.WordTrace tailWord_532687 prefixEnd_532687 273524469401662593362723 := by
  unfold tailWord_532687
  simp only [CollatzResearch.WordTrace]
  refine ⟨19428691021173449541764315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12952460680782299694509543 19428691021173449541764315)
  ·
    refine ⟨29143036531760174312646473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19428691021173449541764315 29143036531760174312646473)
    ·
      refine ⟨21857277398820130734484855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29143036531760174312646473 21857277398820130734484855)
      ·
        refine ⟨32785916098230196101727283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21857277398820130734484855 32785916098230196101727283)
        ·
          refine ⟨49178874147345294152590925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32785916098230196101727283 49178874147345294152590925)
          ·
            refine ⟨18442077805254485307221597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49178874147345294152590925 18442077805254485307221597)
            ·
              refine ⟨6915779176970431990208099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18442077805254485307221597 6915779176970431990208099)
              ·
                refine ⟨10373668765455647985312149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6915779176970431990208099 10373668765455647985312149)
                ·
                  refine ⟨486265723380733499311507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10373668765455647985312149 486265723380733499311507)
                  ·
                    refine ⟨729398585071100248967261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486265723380733499311507 729398585071100248967261)
                    ·
                      refine ⟨273524469401662593362723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729398585071100248967261 273524469401662593362723)
                      ·
                        rfl

theorem cell23_532687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_532687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532687 prefixEnd_532687 := by exact prefixLift 532687
  have htrace : WordTrace (prefixWord ++ tailWord_532687) baseStart_532687 baseEnd_532687 := by
    simpa [prefixWord, tailWord_532687, baseEnd_532687] using wordTrace_append hprefix tailTrace_532687
  have hstable : (prefixWord ++ tailWord_532687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532687).length < 2 ^ (prefixWord ++ tailWord_532687).sum := by decide
  have hdescent : baseEnd_532687 < baseStart_532687 := by decide
  rcases family_descends (prefixWord ++ tailWord_532687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532694 : List Nat := [5, 2, 1, 2, 1, 3, 9]
def baseStart_532694 : Nat := 118140960795 + 532694 * 2 ^ 59
def prefixEnd_532694 : Nat := 4983230072969 + 3 ^ 40 * 532694 * 2
def baseEnd_532694 : Nat := 3376889676126469950311

theorem tailTrace_532694 : CollatzResearch.WordTrace tailWord_532694 prefixEnd_532694 3376889676126469950311 := by
  unfold tailWord_532694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214309145759255608579321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12952630888098726491512757 1214309145759255608579321)
  ·
    refine ⟨910731859319441706434491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1214309145759255608579321 910731859319441706434491)
    ·
      refine ⟨1366097788979162559651737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910731859319441706434491 1366097788979162559651737)
      ·
        refine ⟨1024573341734371919738803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366097788979162559651737 1024573341734371919738803)
        ·
          refine ⟨1536860012601557879608205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024573341734371919738803 1536860012601557879608205)
          ·
            refine ⟨576322504725584204853077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1536860012601557879608205 576322504725584204853077)
            ·
              refine ⟨3376889676126469950311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 576322504725584204853077 3376889676126469950311)
              ·
                rfl

theorem cell23_532694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 9].length) (baseStart_532694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532694 prefixEnd_532694 := by exact prefixLift 532694
  have htrace : WordTrace (prefixWord ++ tailWord_532694) baseStart_532694 baseEnd_532694 := by
    simpa [prefixWord, tailWord_532694, baseEnd_532694] using wordTrace_append hprefix tailTrace_532694
  have hstable : (prefixWord ++ tailWord_532694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532694).length < 2 ^ (prefixWord ++ tailWord_532694).sum := by decide
  have hdescent : baseEnd_532694 < baseStart_532694 := by decide
  rcases family_descends (prefixWord ++ tailWord_532694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532704 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_532704 : Nat := 118140960795 + 532704 * 2 ^ 59
def prefixEnd_532704 : Nat := 4983230072969 + 3 ^ 40 * 532704 * 2
def baseEnd_532704 : Nat := 273533198572789026850145

theorem tailTrace_532704 : CollatzResearch.WordTrace tailWord_532704 prefixEnd_532704 273533198572789026850145 := by
  unfold tailWord_532704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714655531055930722566583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12952874041407907630088777 9714655531055930722566583)
  ·
    refine ⟨14571983296583896083849875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9714655531055930722566583 14571983296583896083849875)
    ·
      refine ⟨21857974944875844125774813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14571983296583896083849875 21857974944875844125774813)
      ·
        refine ⟨8196740604328441547165555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21857974944875844125774813 8196740604328441547165555)
        ·
          refine ⟨12295110906492662320748333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8196740604328441547165555 12295110906492662320748333)
          ·
            refine ⟨4610666589934748370280625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12295110906492662320748333 4610666589934748370280625)
            ·
              refine ⟨3457999942451061277710469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610666589934748370280625 3457999942451061277710469)
              ·
                refine ⟨648374989209573989570713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3457999942451061277710469 648374989209573989570713)
                ·
                  refine ⟨486281241907180492178035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648374989209573989570713 486281241907180492178035)
                  ·
                    refine ⟨729421862860770738267053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486281241907180492178035 729421862860770738267053)
                    ·
                      refine ⟨273533198572789026850145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729421862860770738267053 273533198572789026850145)
                      ·
                        rfl

theorem cell23_532704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_532704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532704 prefixEnd_532704 := by exact prefixLift 532704
  have htrace : WordTrace (prefixWord ++ tailWord_532704) baseStart_532704 baseEnd_532704 := by
    simpa [prefixWord, tailWord_532704, baseEnd_532704] using wordTrace_append hprefix tailTrace_532704
  have hstable : (prefixWord ++ tailWord_532704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532704).length < 2 ^ (prefixWord ++ tailWord_532704).sum := by decide
  have hdescent : baseEnd_532704 < baseStart_532704 := by decide
  rcases family_descends (prefixWord ++ tailWord_532704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532714 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_532714 : Nat := 118140960795 + 532714 * 2 ^ 59
def prefixEnd_532714 : Nat := 4983230072969 + 3 ^ 40 * 532714 * 2
def baseEnd_532714 : Nat := 273538333379333987725099

theorem tailTrace_532714 : CollatzResearch.WordTrace tailWord_532714 prefixEnd_532714 273538333379333987725099 := by
  unfold tailWord_532714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857418948018908288249299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12953117194717088768664797 4857418948018908288249299)
  ·
    refine ⟨7286128422028362432373949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857418948018908288249299 7286128422028362432373949)
    ·
      refine ⟨2732298158260635912140231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7286128422028362432373949 2732298158260635912140231)
      ·
        refine ⟨4098447237390953868210347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732298158260635912140231 4098447237390953868210347)
        ·
          refine ⟨6147670856086430802315521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098447237390953868210347 6147670856086430802315521)
          ·
            refine ⟨4610753142064823101736641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147670856086430802315521 4610753142064823101736641)
            ·
              refine ⟨3458064856548617326302481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610753142064823101736641 3458064856548617326302481)
              ·
                refine ⟨2593548642411462994726861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3458064856548617326302481 2593548642411462994726861)
                ·
                  refine ⟨972580740904298623022573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2593548642411462994726861 972580740904298623022573)
                  ·
                    refine ⟨364717777839111983633465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972580740904298623022573 364717777839111983633465)
                    ·
                      refine ⟨273538333379333987725099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364717777839111983633465 273538333379333987725099)
                      ·
                        rfl

theorem cell23_532714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_532714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532714 prefixEnd_532714 := by exact prefixLift 532714
  have htrace : WordTrace (prefixWord ++ tailWord_532714) baseStart_532714 baseEnd_532714 := by
    simpa [prefixWord, tailWord_532714, baseEnd_532714] using wordTrace_append hprefix tailTrace_532714
  have hstable : (prefixWord ++ tailWord_532714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532714).length < 2 ^ (prefixWord ++ tailWord_532714).sum := by decide
  have hdescent : baseEnd_532714 < baseStart_532714 := by decide
  rcases family_descends (prefixWord ++ tailWord_532714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532720 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_532720 : Nat := 118140960795 + 532720 * 2 ^ 59
def prefixEnd_532720 : Nat := 4983230072969 + 3 ^ 40 * 532720 * 2
def baseEnd_532720 : Nat := 91180471421086988083357

theorem tailTrace_532720 : CollatzResearch.WordTrace tailWord_532720 prefixEnd_532720 91180471421086988083357 := by
  unfold tailWord_532720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714947315026948088857807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12953263086702597451810409 9714947315026948088857807)
  ·
    refine ⟨14572420972540422133286711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9714947315026948088857807 14572420972540422133286711)
    ·
      refine ⟨21858631458810633199930067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14572420972540422133286711 21858631458810633199930067)
      ·
        refine ⟨32787947188215949799895101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21858631458810633199930067 32787947188215949799895101)
        ·
          refine ⟨12295480195580981174960663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32787947188215949799895101 12295480195580981174960663)
          ·
            refine ⟨18443220293371471762440995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12295480195580981174960663 18443220293371471762440995)
            ·
              refine ⟨27664830440057207643661493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18443220293371471762440995 27664830440057207643661493)
              ·
                refine ⟨2593577853755363216593265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27664830440057207643661493 2593577853755363216593265)
                ·
                  refine ⟨1945183390316522412444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593577853755363216593265 1945183390316522412444949)
                  ·
                    refine ⟨91180471421086988083357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1945183390316522412444949 91180471421086988083357)
                    ·
                      rfl

theorem cell23_532720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_532720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532720 prefixEnd_532720 := by exact prefixLift 532720
  have htrace : WordTrace (prefixWord ++ tailWord_532720) baseStart_532720 baseEnd_532720 := by
    simpa [prefixWord, tailWord_532720, baseEnd_532720] using wordTrace_append hprefix tailTrace_532720
  have hstable : (prefixWord ++ tailWord_532720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532720).length < 2 ^ (prefixWord ++ tailWord_532720).sum := by decide
  have hdescent : baseEnd_532720 < baseStart_532720 := by decide
  rcases family_descends (prefixWord ++ tailWord_532720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532721 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_532721 : Nat := 118140960795 + 532721 * 2 ^ 59
def prefixEnd_532721 : Nat := 4983230072969 + 3 ^ 40 * 532721 * 2
def baseEnd_532721 : Nat := 273541927743915460337567

theorem tailTrace_532721 : CollatzResearch.WordTrace tailWord_532721 prefixEnd_532721 273541927743915460337567 := by
  unfold tailWord_532721
  simp only [CollatzResearch.WordTrace]
  refine ⟨19429931103050273348502017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12953287402033515565668011 19429931103050273348502017)
  ·
    refine ⟨14572448327287705011376513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19429931103050273348502017 14572448327287705011376513)
    ·
      refine ⟨10929336245465778758532385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14572448327287705011376513 10929336245465778758532385)
      ·
        refine ⟨8197002184099334068899289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10929336245465778758532385 8197002184099334068899289)
        ·
          refine ⟨6147751638074500551674467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8197002184099334068899289 6147751638074500551674467)
          ·
            refine ⟨9221627457111750827511701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147751638074500551674467 9221627457111750827511701)
            ·
              refine ⟨432263787052113320039611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9221627457111750827511701 432263787052113320039611)
              ·
                refine ⟨648395680578169980059417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432263787052113320039611 648395680578169980059417)
                ·
                  refine ⟨486296760433627485044563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648395680578169980059417 486296760433627485044563)
                  ·
                    refine ⟨729445140650441227566845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486296760433627485044563 729445140650441227566845)
                    ·
                      refine ⟨273541927743915460337567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729445140650441227566845 273541927743915460337567)
                      ·
                        rfl

theorem cell23_532721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_532721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532721 prefixEnd_532721 := by exact prefixLift 532721
  have htrace : WordTrace (prefixWord ++ tailWord_532721) baseStart_532721 baseEnd_532721 := by
    simpa [prefixWord, tailWord_532721, baseEnd_532721] using wordTrace_append hprefix tailTrace_532721
  have hstable : (prefixWord ++ tailWord_532721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532721).length < 2 ^ (prefixWord ++ tailWord_532721).sum := by decide
  have hdescent : baseEnd_532721 < baseStart_532721 := by decide
  rcases family_descends (prefixWord ++ tailWord_532721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532744 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_532744 : Nat := 118140960795 + 532744 * 2 ^ 59
def prefixEnd_532744 : Nat := 4983230072969 + 3 ^ 40 * 532744 * 2
def baseEnd_532744 : Nat := 273553737798968870349961

theorem tailTrace_532744 : CollatzResearch.WordTrace tailWord_532744 prefixEnd_532744 273553737798968870349961 := by
  unfold tailWord_532744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715384990983474138294643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12953846654644632184392857 9715384990983474138294643)
  ·
    refine ⟨14573077486475211207441965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9715384990983474138294643 14573077486475211207441965)
    ·
      refine ⟨5464904057428204202790737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14573077486475211207441965 5464904057428204202790737)
      ·
        refine ⟨4098678043071153152093053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5464904057428204202790737 4098678043071153152093053)
        ·
          refine ⟨1537004266151682432034895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4098678043071153152093053 1537004266151682432034895)
          ·
            refine ⟨2305506399227523648052343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537004266151682432034895 2305506399227523648052343)
            ·
              refine ⟨3458259598841285472078515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305506399227523648052343 3458259598841285472078515)
              ·
                refine ⟨5187389398261928208117773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458259598841285472078515 5187389398261928208117773)
                ·
                  refine ⟨1945271024348223078044165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5187389398261928208117773 1945271024348223078044165)
                  ·
                    refine ⟨364738317065291827133281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945271024348223078044165 364738317065291827133281)
                    ·
                      refine ⟨273553737798968870349961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364738317065291827133281 273553737798968870349961)
                      ·
                        rfl

theorem cell23_532744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_532744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532744 prefixEnd_532744 := by exact prefixLift 532744
  have htrace : WordTrace (prefixWord ++ tailWord_532744) baseStart_532744 baseEnd_532744 := by
    simpa [prefixWord, tailWord_532744, baseEnd_532744] using wordTrace_append hprefix tailTrace_532744
  have hstable : (prefixWord ++ tailWord_532744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532744).length < 2 ^ (prefixWord ++ tailWord_532744).sum := by decide
  have hdescent : baseEnd_532744 < baseStart_532744 := by decide
  rcases family_descends (prefixWord ++ tailWord_532744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532778 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_532778 : Nat := 118140960795 + 532778 * 2 ^ 59
def prefixEnd_532778 : Nat := 4983230072969 + 3 ^ 40 * 532778 * 2
def baseEnd_532778 : Nat := 273571196141221737324805

theorem tailTrace_532778 : CollatzResearch.WordTrace tailWord_532778 prefixEnd_532778 273571196141221737324805 := by
  unfold tailWord_532778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858002515960943020831747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12954673375895848055551325 4858002515960943020831747)
  ·
    refine ⟨7287003773941414531247621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4858002515960943020831747 7287003773941414531247621)
    ·
      refine ⟨1366313207614015224608929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7287003773941414531247621 1366313207614015224608929)
      ·
        refine ⟨1024734905710511418456697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366313207614015224608929 1024734905710511418456697)
        ·
          refine ⟨768551179282883563842523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024734905710511418456697 768551179282883563842523)
          ·
            refine ⟨1152826768924325345763785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768551179282883563842523 1152826768924325345763785)
            ·
              refine ⟨864620076693244009322839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152826768924325345763785 864620076693244009322839)
              ·
                refine ⟨1296930115039866013984259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864620076693244009322839 1296930115039866013984259)
                ·
                  refine ⟨1945395172559799020976389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296930115039866013984259 1945395172559799020976389)
                  ·
                    refine ⟨364761594854962316433073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1945395172559799020976389 364761594854962316433073)
                    ·
                      refine ⟨273571196141221737324805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364761594854962316433073 273571196141221737324805)
                      ·
                        rfl

theorem cell23_532778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_532778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532778 prefixEnd_532778 := by exact prefixLift 532778
  have htrace : WordTrace (prefixWord ++ tailWord_532778) baseStart_532778 baseEnd_532778 := by
    simpa [prefixWord, tailWord_532778, baseEnd_532778] using wordTrace_append hprefix tailTrace_532778
  have hstable : (prefixWord ++ tailWord_532778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532778).length < 2 ^ (prefixWord ++ tailWord_532778).sum := by decide
  have hdescent : baseEnd_532778 < baseStart_532778 := by decide
  rcases family_descends (prefixWord ++ tailWord_532778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532834 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_532834 : Nat := 118140960795 + 532834 * 2 ^ 59
def prefixEnd_532834 : Nat := 4983230072969 + 3 ^ 40 * 532834 * 2
def baseEnd_532834 : Nat := 273599951057873518224547

theorem tailTrace_532834 : CollatzResearch.WordTrace tailWord_532834 prefixEnd_532834 273599951057873518224547 := by
  unfold tailWord_532834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858513137910223411841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12956035034427262431577037 4858513137910223411841389)
  ·
    refine ⟨1821942426716333779440521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4858513137910223411841389 1821942426716333779440521)
    ·
      refine ⟨1366456820037250334580391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1821942426716333779440521 1366456820037250334580391)
      ·
        refine ⟨2049685230055875501870587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366456820037250334580391 2049685230055875501870587)
        ·
          refine ⟨3074527845083813252805881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049685230055875501870587 3074527845083813252805881)
          ·
            refine ⟨2305895883812859939604411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3074527845083813252805881 2305895883812859939604411)
            ·
              refine ⟨3458843825719289909406617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305895883812859939604411 3458843825719289909406617)
              ·
                refine ⟨2594132869289467432054963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3458843825719289909406617 2594132869289467432054963)
                ·
                  refine ⟨3891199303934201148082445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2594132869289467432054963 3891199303934201148082445)
                  ·
                    refine ⟨1459199738975325430530917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3891199303934201148082445 1459199738975325430530917)
                    ·
                      refine ⟨273599951057873518224547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1459199738975325430530917 273599951057873518224547)
                      ·
                        rfl

theorem cell23_532834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_532834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532834 prefixEnd_532834 := by exact prefixLift 532834
  have htrace : WordTrace (prefixWord ++ tailWord_532834) baseStart_532834 baseEnd_532834 := by
    simpa [prefixWord, tailWord_532834, baseEnd_532834] using wordTrace_append hprefix tailTrace_532834
  have hstable : (prefixWord ++ tailWord_532834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532834).length < 2 ^ (prefixWord ++ tailWord_532834).sum := by decide
  have hdescent : baseEnd_532834 < baseStart_532834 := by decide
  rcases family_descends (prefixWord ++ tailWord_532834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532878 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_532878 : Nat := 118140960795 + 532878 * 2 ^ 59
def prefixEnd_532878 : Nat := 4983230072969 + 3 ^ 40 * 532878 * 2
def baseEnd_532878 : Nat := 91207514735557115358115

theorem tailTrace_532878 : CollatzResearch.WordTrace tailWord_532878 prefixEnd_532878 91207514735557115358115 := by
  unfold tailWord_532878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429457170435186145245911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12957104908987659441311525 2429457170435186145245911)
  ·
    refine ⟨3644185755652779217868867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429457170435186145245911 3644185755652779217868867)
    ·
      refine ⟨5466278633479168826803301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644185755652779217868867 5466278633479168826803301)
      ·
        refine ⟨1024927243777344155025619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5466278633479168826803301 1024927243777344155025619)
        ·
          refine ⟨1537390865666016232538429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024927243777344155025619 1537390865666016232538429)
          ·
            refine ⟨576521574624756087201911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1537390865666016232538429 576521574624756087201911)
            ·
              refine ⟨864782361937134130802867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576521574624756087201911 864782361937134130802867)
              ·
                refine ⟨1297173542905701196204301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864782361937134130802867 1297173542905701196204301)
                ·
                  refine ⟨486440078589637948576613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1297173542905701196204301 486440078589637948576613)
                  ·
                    refine ⟨91207514735557115358115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486440078589637948576613 91207514735557115358115)
                    ·
                      rfl

theorem cell23_532878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_532878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532878 prefixEnd_532878 := by exact prefixLift 532878
  have htrace : WordTrace (prefixWord ++ tailWord_532878) baseStart_532878 baseEnd_532878 := by
    simpa [prefixWord, tailWord_532878, baseEnd_532878] using wordTrace_append hprefix tailTrace_532878
  have hstable : (prefixWord ++ tailWord_532878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532878).length < 2 ^ (prefixWord ++ tailWord_532878).sum := by decide
  have hdescent : baseEnd_532878 < baseStart_532878 := by decide
  rcases family_descends (prefixWord ++ tailWord_532878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532935 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_532935 : Nat := 118140960795 + 532935 * 2 ^ 59
def prefixEnd_532935 : Nat := 4983230072969 + 3 ^ 40 * 532935 * 2
def baseEnd_532935 : Nat := 273651812603977623061583

theorem tailTrace_532935 : CollatzResearch.WordTrace tailWord_532935 prefixEnd_532935 273651812603977623061583 := by
  unfold tailWord_532935
  simp only [CollatzResearch.WordTrace]
  refine ⟨19437736324274987896792259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12958490882849991931194839 19437736324274987896792259)
  ·
    refine ⟨29156604486412481845188389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19437736324274987896792259 29156604486412481845188389)
    ·
      refine ⟨5466863341202340345972823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29156604486412481845188389 5466863341202340345972823)
      ·
        refine ⟨8200295011803510518959235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466863341202340345972823 8200295011803510518959235)
        ·
          refine ⟨12300442517705265778438853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200295011803510518959235 12300442517705265778438853)
          ·
            refine ⟨2306332972069737333457285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12300442517705265778438853 2306332972069737333457285)
            ·
              refine ⟨432437432263075750023241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2306332972069737333457285 432437432263075750023241)
              ·
                refine ⟨324328074197306812517431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432437432263075750023241 324328074197306812517431)
                ·
                  refine ⟨486492111295960218776147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324328074197306812517431 486492111295960218776147)
                  ·
                    refine ⟨729738166943940328164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486492111295960218776147 729738166943940328164221)
                    ·
                      refine ⟨273651812603977623061583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729738166943940328164221 273651812603977623061583)
                      ·
                        rfl

theorem cell23_532935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_532935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532935 prefixEnd_532935 := by exact prefixLift 532935
  have htrace : WordTrace (prefixWord ++ tailWord_532935) baseStart_532935 baseEnd_532935 := by
    simpa [prefixWord, tailWord_532935, baseEnd_532935] using wordTrace_append hprefix tailTrace_532935
  have hstable : (prefixWord ++ tailWord_532935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532935).length < 2 ^ (prefixWord ++ tailWord_532935).sum := by decide
  have hdescent : baseEnd_532935 < baseStart_532935 := by decide
  rcases family_descends (prefixWord ++ tailWord_532935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532937 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_532937 : Nat := 118140960795 + 532937 * 2 ^ 59
def prefixEnd_532937 : Nat := 4983230072969 + 3 ^ 40 * 532937 * 2
def baseEnd_532937 : Nat := 273652839565286615236573

theorem tailTrace_532937 : CollatzResearch.WordTrace tailWord_532937 prefixEnd_532937 273652839565286615236573 := by
  unfold tailWord_532937
  simp only [CollatzResearch.WordTrace]
  refine ⟨19437809270267742238365065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12958539513511828158910043 19437809270267742238365065)
  ·
    refine ⟨14578356952700806678773799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19437809270267742238365065 14578356952700806678773799)
    ·
      refine ⟨21867535429051210018160699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14578356952700806678773799 21867535429051210018160699)
      ·
        refine ⟨32801303143576815027241049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21867535429051210018160699 32801303143576815027241049)
        ·
          refine ⟨24600977357682611270430787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32801303143576815027241049 24600977357682611270430787)
          ·
            refine ⟨36901466036523916905646181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24600977357682611270430787 36901466036523916905646181)
            ·
              refine ⟨6919024881848234419808659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36901466036523916905646181 6919024881848234419808659)
              ·
                refine ⟨10378537322772351629712989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6919024881848234419808659 10378537322772351629712989)
                ·
                  refine ⟨3891951496039631861142371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10378537322772351629712989 3891951496039631861142371)
                  ·
                    refine ⟨5837927244059447791713557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3891951496039631861142371 5837927244059447791713557)
                    ·
                      refine ⟨273652839565286615236573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5837927244059447791713557 273652839565286615236573)
                      ·
                        rfl

theorem cell23_532937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_532937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532937 prefixEnd_532937 := by exact prefixLift 532937
  have htrace : WordTrace (prefixWord ++ tailWord_532937) baseStart_532937 baseEnd_532937 := by
    simpa [prefixWord, tailWord_532937, baseEnd_532937] using wordTrace_append hprefix tailTrace_532937
  have hstable : (prefixWord ++ tailWord_532937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532937).length < 2 ^ (prefixWord ++ tailWord_532937).sum := by decide
  have hdescent : baseEnd_532937 < baseStart_532937 := by decide
  rcases family_descends (prefixWord ++ tailWord_532937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532961 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_532961 : Nat := 118140960795 + 532961 * 2 ^ 59
def prefixEnd_532961 : Nat := 4983230072969 + 3 ^ 40 * 532961 * 2
def baseEnd_532961 : Nat := 273665163100994521336463

theorem tailTrace_532961 : CollatzResearch.WordTrace tailWord_532961 prefixEnd_532961 273665163100994521336463 := by
  unfold tailWord_532961
  simp only [CollatzResearch.WordTrace]
  refine ⟨19438684622180794337238737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959123081453862891492491 19438684622180794337238737)
  ·
    refine ⟨14579013466635595752929053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19438684622180794337238737 14579013466635595752929053)
    ·
      refine ⟨5467130049988348407348395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14579013466635595752929053 5467130049988348407348395)
      ·
        refine ⟨8200695074982522611022593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467130049988348407348395 8200695074982522611022593)
        ·
          refine ⟨6150521306236891958266945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8200695074982522611022593 6150521306236891958266945)
          ·
            refine ⟨4612890979677668968700209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6150521306236891958266945 4612890979677668968700209)
            ·
              refine ⟨3459668234758251726525157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4612890979677668968700209 3459668234758251726525157)
              ·
                refine ⟨648687794017172198723467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3459668234758251726525157 648687794017172198723467)
                ·
                  refine ⟨973031691025758298085201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648687794017172198723467 973031691025758298085201)
                  ·
                    refine ⟨729773768269318723563901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 973031691025758298085201 729773768269318723563901)
                    ·
                      refine ⟨273665163100994521336463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729773768269318723563901 273665163100994521336463)
                      ·
                        rfl

theorem cell23_532961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_532961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532961 prefixEnd_532961 := by exact prefixLift 532961
  have htrace : WordTrace (prefixWord ++ tailWord_532961) baseStart_532961 baseEnd_532961 := by
    simpa [prefixWord, tailWord_532961, baseEnd_532961] using wordTrace_append hprefix tailTrace_532961
  have hstable : (prefixWord ++ tailWord_532961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532961).length < 2 ^ (prefixWord ++ tailWord_532961).sum := by decide
  have hdescent : baseEnd_532961 < baseStart_532961 := by decide
  rcases family_descends (prefixWord ++ tailWord_532961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532981 : List Nat := [1, 3, 5, 1, 2, 1, 10]
def baseStart_532981 : Nat := 118140960795 + 532981 * 2 ^ 59
def prefixEnd_532981 : Nat := 4983230072969 + 3 ^ 40 * 532981 * 2
def baseEnd_532981 : Nat := 3378709045852894359091

theorem tailTrace_532981 : CollatzResearch.WordTrace tailWord_532981 prefixEnd_532981 3378709045852894359091 := by
  unfold tailWord_532981
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439414082108337752966797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959609388072225168644531 19439414082108337752966797)
  ·
    refine ⟨7289780280790626657362549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19439414082108337752966797 7289780280790626657362549)
    ·
      refine ⟨683416901324121249127739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7289780280790626657362549 683416901324121249127739)
      ·
        refine ⟨1025125351986181873691609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683416901324121249127739 1025125351986181873691609)
        ·
          refine ⟨768844013989636405268707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025125351986181873691609 768844013989636405268707)
          ·
            refine ⟨1153266020984454607903061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768844013989636405268707 1153266020984454607903061)
            ·
              refine ⟨3378709045852894359091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1153266020984454607903061 3378709045852894359091)
              ·
                rfl

theorem cell23_532981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 10].length) (baseStart_532981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532981 prefixEnd_532981 := by exact prefixLift 532981
  have htrace : WordTrace (prefixWord ++ tailWord_532981) baseStart_532981 baseEnd_532981 := by
    simpa [prefixWord, tailWord_532981, baseEnd_532981] using wordTrace_append hprefix tailTrace_532981
  have hstable : (prefixWord ++ tailWord_532981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532981).length < 2 ^ (prefixWord ++ tailWord_532981).sum := by decide
  have hdescent : baseEnd_532981 < baseStart_532981 := by decide
  rcases family_descends (prefixWord ++ tailWord_532981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532987 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_532987 : Nat := 118140960795 + 532987 * 2 ^ 59
def prefixEnd_532987 : Nat := 4983230072969 + 3 ^ 40 * 532987 * 2
def baseEnd_532987 : Nat := 273678513598011419611343

theorem tailTrace_532987 : CollatzResearch.WordTrace tailWord_532987 prefixEnd_532987 273678513598011419611343 := by
  unfold tailWord_532987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439632920086600777685215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959755280057733851790143 19439632920086600777685215)
  ·
    refine ⟨29159449380129901166527823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19439632920086600777685215 29159449380129901166527823)
    ·
      refine ⟨43739174070194851749791735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29159449380129901166527823 43739174070194851749791735)
      ·
        refine ⟨65608761105292277624687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43739174070194851749791735 65608761105292277624687603)
        ·
          refine ⟨98413141657938416437031405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65608761105292277624687603 98413141657938416437031405)
          ·
            refine ⟨36904928121726906163886777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98413141657938416437031405 36904928121726906163886777)
            ·
              refine ⟨27678696091295179622915083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36904928121726906163886777 27678696091295179622915083)
              ·
                refine ⟨41518044136942769434372625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27678696091295179622915083 41518044136942769434372625)
                ·
                  refine ⟨31138533102707077075779469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41518044136942769434372625 31138533102707077075779469)
                  ·
                    refine ⟨11676949913515153903417301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31138533102707077075779469 11676949913515153903417301)
                    ·
                      refine ⟨273678513598011419611343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11676949913515153903417301 273678513598011419611343)
                      ·
                        rfl

theorem cell23_532987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_532987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532987 prefixEnd_532987 := by exact prefixLift 532987
  have htrace : WordTrace (prefixWord ++ tailWord_532987) baseStart_532987 baseEnd_532987 := by
    simpa [prefixWord, tailWord_532987, baseEnd_532987] using wordTrace_append hprefix tailTrace_532987
  have hstable : (prefixWord ++ tailWord_532987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532987).length < 2 ^ (prefixWord ++ tailWord_532987).sum := by decide
  have hdescent : baseEnd_532987 < baseStart_532987 := by decide
  rcases family_descends (prefixWord ++ tailWord_532987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_532991 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_532991 : Nat := 118140960795 + 532991 * 2 ^ 59
def prefixEnd_532991 : Nat := 4983230072969 + 3 ^ 40 * 532991 * 2
def baseEnd_532991 : Nat := 273680567520629403961325

theorem tailTrace_532991 : CollatzResearch.WordTrace tailWord_532991 prefixEnd_532991 273680567520629403961325 := by
  unfold tailWord_532991
  simp only [CollatzResearch.WordTrace]
  refine ⟨19439778812072109460830827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12959852541381406307220551 19439778812072109460830827)
  ·
    refine ⟨29159668218108164191246241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19439778812072109460830827 29159668218108164191246241)
    ·
      refine ⟨21869751163581123143434681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29159668218108164191246241 21869751163581123143434681)
      ·
        refine ⟨16402313372685842357576011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21869751163581123143434681 16402313372685842357576011)
        ·
          refine ⟨24603470059028763536364017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16402313372685842357576011 24603470059028763536364017)
          ·
            refine ⟨18452602544271572652273013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24603470059028763536364017 18452602544271572652273013)
            ·
              refine ⟨1729931488525459936150595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18452602544271572652273013 1729931488525459936150595)
              ·
                refine ⟨2594897232788189904225893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729931488525459936150595 2594897232788189904225893)
                ·
                  refine ⟨486543231147785607042355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2594897232788189904225893 486543231147785607042355)
                  ·
                    refine ⟨729814846721678410563533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486543231147785607042355 729814846721678410563533)
                    ·
                      refine ⟨273680567520629403961325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 729814846721678410563533 273680567520629403961325)
                      ·
                        rfl

theorem cell23_532991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_532991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_532991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_532991 prefixEnd_532991 := by exact prefixLift 532991
  have htrace : WordTrace (prefixWord ++ tailWord_532991) baseStart_532991 baseEnd_532991 := by
    simpa [prefixWord, tailWord_532991, baseEnd_532991] using wordTrace_append hprefix tailTrace_532991
  have hstable : (prefixWord ++ tailWord_532991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_532991).length < 2 ^ (prefixWord ++ tailWord_532991).sum := by decide
  have hdescent : baseEnd_532991 < baseStart_532991 := by decide
  rcases family_descends (prefixWord ++ tailWord_532991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 3, 3, 2]
def baseStart_533001 : Nat := 118140960795 + 533001 * 2 ^ 59
def prefixEnd_533001 : Nat := 4983230072969 + 3 ^ 40 * 533001 * 2
def baseEnd_533001 : Nat := 273685702327174364836279

theorem tailTrace_533001 : CollatzResearch.WordTrace tailWord_533001 prefixEnd_533001 273685702327174364836279 := by
  unfold tailWord_533001
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440143542035881168694857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12960095694690587445796571 19440143542035881168694857)
  ·
    refine ⟨14580107656526910876521143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19440143542035881168694857 14580107656526910876521143)
    ·
      refine ⟨21870161484790366314781715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14580107656526910876521143 21870161484790366314781715)
      ·
        refine ⟨32805242227185549472172573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870161484790366314781715 32805242227185549472172573)
        ·
          refine ⟨12301965835194581052064715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32805242227185549472172573 12301965835194581052064715)
          ·
            refine ⟨18452948752791871578097073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12301965835194581052064715 18452948752791871578097073)
            ·
              refine ⟨13839711564593903683572805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18452948752791871578097073 13839711564593903683572805)
              ·
                refine ⟨2594945918361356940669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13839711564593903683572805 2594945918361356940669901)
                ·
                  refine ⟨973104719385508852751213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2594945918361356940669901 973104719385508852751213)
                  ·
                    refine ⟨364914269769565819781705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973104719385508852751213 364914269769565819781705)
                    ·
                      refine ⟨273685702327174364836279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364914269769565819781705 273685702327174364836279)
                      ·
                        rfl

theorem cell23_533001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 3, 2].length) (baseStart_533001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533001 prefixEnd_533001 := by exact prefixLift 533001
  have htrace : WordTrace (prefixWord ++ tailWord_533001) baseStart_533001 baseEnd_533001 := by
    simpa [prefixWord, tailWord_533001, baseEnd_533001] using wordTrace_append hprefix tailTrace_533001
  have hstable : (prefixWord ++ tailWord_533001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533001).length < 2 ^ (prefixWord ++ tailWord_533001).sum := by decide
  have hdescent : baseEnd_533001 < baseStart_533001 := by decide
  rcases family_descends (prefixWord ++ tailWord_533001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533005 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_533005 : Nat := 118140960795 + 533005 * 2 ^ 59
def prefixEnd_533005 : Nat := 4983230072969 + 3 ^ 40 * 533005 * 2
def baseEnd_533005 : Nat := 273687756249792349186261

theorem tailTrace_533005 : CollatzResearch.WordTrace tailWord_533005 prefixEnd_533005 273687756249792349186261 := by
  unfold tailWord_533005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440289434021389851840469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12960192956014259901226979 19440289434021389851840469)
  ·
    refine ⟨455631783609876324652511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19440289434021389851840469 455631783609876324652511)
    ·
      refine ⟨683447675414814486978767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455631783609876324652511 683447675414814486978767)
      ·
        refine ⟨1025171513122221730468151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683447675414814486978767 1025171513122221730468151)
        ·
          refine ⟨1537757269683332595702227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025171513122221730468151 1537757269683332595702227)
          ·
            refine ⟨2306635904524998893553341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537757269683332595702227 2306635904524998893553341)
            ·
              refine ⟨864988464196874585082503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2306635904524998893553341 864988464196874585082503)
              ·
                refine ⟨1297482696295311877623755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864988464196874585082503 1297482696295311877623755)
                ·
                  refine ⟨1946224044442967816435633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1297482696295311877623755 1946224044442967816435633)
                  ·
                    refine ⟨1459668033332225862326725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1946224044442967816435633 1459668033332225862326725)
                    ·
                      refine ⟨273687756249792349186261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1459668033332225862326725 273687756249792349186261)
                      ·
                        rfl

theorem cell23_533005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_533005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533005 prefixEnd_533005 := by exact prefixLift 533005
  have htrace : WordTrace (prefixWord ++ tailWord_533005) baseStart_533005 baseEnd_533005 := by
    simpa [prefixWord, tailWord_533005, baseEnd_533005] using wordTrace_append hprefix tailTrace_533005
  have hstable : (prefixWord ++ tailWord_533005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533005).length < 2 ^ (prefixWord ++ tailWord_533005).sum := by decide
  have hdescent : baseEnd_533005 < baseStart_533005 := by decide
  rcases family_descends (prefixWord ++ tailWord_533005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533015 : List Nat := [1, 1, 3, 6, 2, 1, 2, 7]
def baseStart_533015 : Nat := 118140960795 + 533015 * 2 ^ 59
def prefixEnd_533015 : Nat := 4983230072969 + 3 ^ 40 * 533015 * 2
def baseEnd_533015 : Nat := 10136773742827307780045

theorem tailTrace_533015 : CollatzResearch.WordTrace tailWord_533015 prefixEnd_533015 10136773742827307780045 := by
  unfold tailWord_533015
  simp only [CollatzResearch.WordTrace]
  refine ⟨19440654163985161559704499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12960436109323441039802999 19440654163985161559704499)
  ·
    refine ⟨29160981245977742339556749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19440654163985161559704499 29160981245977742339556749)
    ·
      refine ⟨10935367967241653377333781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29160981245977742339556749 10935367967241653377333781)
      ·
        refine ⟨512595373464452502062521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10935367967241653377333781 512595373464452502062521)
        ·
          refine ⟨384446530098339376546891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512595373464452502062521 384446530098339376546891)
          ·
            refine ⟨576669795147509064820337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384446530098339376546891 576669795147509064820337)
            ·
              refine ⟨432502346360631798615253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576669795147509064820337 432502346360631798615253)
              ·
                refine ⟨10136773742827307780045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 432502346360631798615253 10136773742827307780045)
                ·
                  rfl

theorem cell23_533015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 7].length) (baseStart_533015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533015 prefixEnd_533015 := by exact prefixLift 533015
  have htrace : WordTrace (prefixWord ++ tailWord_533015) baseStart_533015 baseEnd_533015 := by
    simpa [prefixWord, tailWord_533015, baseEnd_533015] using wordTrace_append hprefix tailTrace_533015
  have hstable : (prefixWord ++ tailWord_533015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533015).length < 2 ^ (prefixWord ++ tailWord_533015).sum := by decide
  have hdescent : baseEnd_533015 < baseStart_533015 := by decide
  rcases family_descends (prefixWord ++ tailWord_533015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533018 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_533018 : Nat := 118140960795 + 533018 * 2 ^ 59
def prefixEnd_533018 : Nat := 4983230072969 + 3 ^ 40 * 533018 * 2
def baseEnd_533018 : Nat := 273694431498300798323701

theorem tailTrace_533018 : CollatzResearch.WordTrace tailWord_533018 prefixEnd_533018 273694431498300798323701 := by
  unfold tailWord_533018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860190895743573268015927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12960509055316195381375805 4860190895743573268015927)
  ·
    refine ⟨7290286343615359902023891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4860190895743573268015927 7290286343615359902023891)
    ·
      refine ⟨10935429515423039853035837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7290286343615359902023891 10935429515423039853035837)
      ·
        refine ⟨4100786068283639944888439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10935429515423039853035837 4100786068283639944888439)
        ·
          refine ⟨6151179102425459917332659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100786068283639944888439 6151179102425459917332659)
          ·
            refine ⟨9226768653638189875998989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6151179102425459917332659 9226768653638189875998989)
            ·
              refine ⟨3460038245114321203499621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9226768653638189875998989 3460038245114321203499621)
              ·
                refine ⟨648757170958935225656179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3460038245114321203499621 648757170958935225656179)
                ·
                  refine ⟨973135756438402838484269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648757170958935225656179 973135756438402838484269)
                  ·
                    refine ⟨364925908664401064431601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973135756438402838484269 364925908664401064431601)
                    ·
                      refine ⟨273694431498300798323701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364925908664401064431601 273694431498300798323701)
                      ·
                        rfl

theorem cell23_533018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_533018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533018 prefixEnd_533018 := by exact prefixLift 533018
  have htrace : WordTrace (prefixWord ++ tailWord_533018) baseStart_533018 baseEnd_533018 := by
    simpa [prefixWord, tailWord_533018, baseEnd_533018] using wordTrace_append hprefix tailTrace_533018
  have hstable : (prefixWord ++ tailWord_533018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533018).length < 2 ^ (prefixWord ++ tailWord_533018).sum := by decide
  have hdescent : baseEnd_533018 < baseStart_533018 := by decide
  rcases family_descends (prefixWord ++ tailWord_533018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533048 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_533048 : Nat := 118140960795 + 533048 * 2 ^ 59
def prefixEnd_533048 : Nat := 4983230072969 + 3 ^ 40 * 533048 * 2
def baseEnd_533048 : Nat := 273709835917935680948563

theorem tailTrace_533048 : CollatzResearch.WordTrace tailWord_533048 prefixEnd_533048 273709835917935680948563 := by
  unfold tailWord_533048
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720928886432804097827899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12961238515243738797103865 9720928886432804097827899)
  ·
    refine ⟨14581393329649206146741849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9720928886432804097827899 14581393329649206146741849)
    ·
      refine ⟨10936044997236904610056387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14581393329649206146741849 10936044997236904610056387)
      ·
        refine ⟨16404067495855356915084581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10936044997236904610056387 16404067495855356915084581)
        ·
          refine ⟨3075762655472879421578359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16404067495855356915084581 3075762655472879421578359)
          ·
            refine ⟨4613643983209319132367539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075762655472879421578359 4613643983209319132367539)
            ·
              refine ⟨6920465974813978698551309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4613643983209319132367539 6920465974813978698551309)
              ·
                refine ⟨2595174740555242011956741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6920465974813978698551309 2595174740555242011956741)
                ·
                  refine ⟨486595263854107877241889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2595174740555242011956741 486595263854107877241889)
                  ·
                    refine ⟨364946447890580907931417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486595263854107877241889 364946447890580907931417)
                    ·
                      refine ⟨273709835917935680948563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 364946447890580907931417 273709835917935680948563)
                      ·
                        rfl

theorem cell23_533048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_533048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533048 prefixEnd_533048 := by exact prefixLift 533048
  have htrace : WordTrace (prefixWord ++ tailWord_533048) baseStart_533048 baseEnd_533048 := by
    simpa [prefixWord, tailWord_533048, baseEnd_533048] using wordTrace_append hprefix tailTrace_533048
  have hstable : (prefixWord ++ tailWord_533048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533048).length < 2 ^ (prefixWord ++ tailWord_533048).sum := by decide
  have hdescent : baseEnd_533048 < baseStart_533048 := by decide
  rcases family_descends (prefixWord ++ tailWord_533048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533121 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_533121 : Nat := 118140960795 + 533121 * 2 ^ 59
def prefixEnd_533121 : Nat := 4983230072969 + 3 ^ 40 * 533121 * 2
def baseEnd_533121 : Nat := 273747320005713895335727

theorem tailTrace_533121 : CollatzResearch.WordTrace tailWord_533121 prefixEnd_533121 273747320005713895335727 := by
  unfold tailWord_533121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19444520301601141663063217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12963013534400761108708811 19444520301601141663063217)
  ·
    refine ⟨14583390226200856247297413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19444520301601141663063217 14583390226200856247297413)
    ·
      refine ⟨2734385667412660546368265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14583390226200856247297413 2734385667412660546368265)
      ·
        refine ⟨2050789250559495409776199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734385667412660546368265 2050789250559495409776199)
        ·
          refine ⟨3076183875839243114664299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050789250559495409776199 3076183875839243114664299)
          ·
            refine ⟨4614275813758864671996449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3076183875839243114664299 4614275813758864671996449)
            ·
              refine ⟨3460706860319148503997337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4614275813758864671996449 3460706860319148503997337)
              ·
                refine ⟨2595530145239361377998003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460706860319148503997337 2595530145239361377998003)
                ·
                  refine ⟨3893295217859042066997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595530145239361377998003 3893295217859042066997005)
                  ·
                    refine ⟨1459985706697140775123877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3893295217859042066997005 1459985706697140775123877)
                    ·
                      refine ⟨273747320005713895335727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1459985706697140775123877 273747320005713895335727)
                      ·
                        rfl

theorem cell23_533121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_533121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533121 prefixEnd_533121 := by exact prefixLift 533121
  have htrace : WordTrace (prefixWord ++ tailWord_533121) baseStart_533121 baseEnd_533121 := by
    simpa [prefixWord, tailWord_533121, baseEnd_533121] using wordTrace_append hprefix tailTrace_533121
  have hstable : (prefixWord ++ tailWord_533121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533121).length < 2 ^ (prefixWord ++ tailWord_533121).sum := by decide
  have hdescent : baseEnd_533121 < baseStart_533121 := by decide
  rcases family_descends (prefixWord ++ tailWord_533121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533122 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 7]
def baseStart_533122 : Nat := 118140960795 + 533122 * 2 ^ 59
def prefixEnd_533122 : Nat := 4983230072969 + 3 ^ 40 * 533122 * 2
def baseEnd_533122 : Nat := 30416425942929821269247

theorem tailTrace_533122 : CollatzResearch.WordTrace tailWord_533122 prefixEnd_533122 30416425942929821269247 := by
  unfold tailWord_533122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861139193649379708462405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12963037849731679222566413 4861139193649379708462405)
  ·
    refine ⟨911463598809258695336701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4861139193649379708462405 911463598809258695336701)
    ·
      refine ⟨341798849553472010751263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 911463598809258695336701 341798849553472010751263)
      ·
        refine ⟨512698274330208016126895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341798849553472010751263 512698274330208016126895)
        ·
          refine ⟨769047411495312024190343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512698274330208016126895 769047411495312024190343)
          ·
            refine ⟨1153571117242968036285515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769047411495312024190343 1153571117242968036285515)
            ·
              refine ⟨1730356675864452054428273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153571117242968036285515 1730356675864452054428273)
              ·
                refine ⟨1297767506898339040821205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730356675864452054428273 1297767506898339040821205)
                ·
                  refine ⟨30416425942929821269247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1297767506898339040821205 30416425942929821269247)
                  ·
                    rfl

theorem cell23_533122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_533122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533122 prefixEnd_533122 := by exact prefixLift 533122
  have htrace : WordTrace (prefixWord ++ tailWord_533122) baseStart_533122 baseEnd_533122 := by
    simpa [prefixWord, tailWord_533122, baseEnd_533122] using wordTrace_append hprefix tailTrace_533122
  have hstable : (prefixWord ++ tailWord_533122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533122).length < 2 ^ (prefixWord ++ tailWord_533122).sum := by decide
  have hdescent : baseEnd_533122 < baseStart_533122 := by decide
  rcases family_descends (prefixWord ++ tailWord_533122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533138 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_533138 : Nat := 118140960795 + 533138 * 2 ^ 59
def prefixEnd_533138 : Nat := 4983230072969 + 3 ^ 40 * 533138 * 2
def baseEnd_533138 : Nat := 273756049176840328823149

theorem tailTrace_533138 : CollatzResearch.WordTrace tailWord_533138 prefixEnd_533138 273756049176840328823149 := by
  unfold tailWord_533138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861285085634888391608017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12963426895026369044288045 4861285085634888391608017)
  ·
    refine ⟨3645963814226166293706013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4861285085634888391608017 3645963814226166293706013)
    ·
      refine ⟨1367236430334812360139755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3645963814226166293706013 1367236430334812360139755)
      ·
        refine ⟨2050854645502218540209633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367236430334812360139755 2050854645502218540209633)
        ·
          refine ⟨1538140984126663905157225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050854645502218540209633 1538140984126663905157225)
          ·
            refine ⟨1153605738094997928867919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1538140984126663905157225 1153605738094997928867919)
            ·
              refine ⟨1730408607142496893301879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153605738094997928867919 1730408607142496893301879)
              ·
                refine ⟨2595612910713745339952819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730408607142496893301879 2595612910713745339952819)
                ·
                  refine ⟨3893419366070618009929229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2595612910713745339952819 3893419366070618009929229)
                  ·
                    refine ⟨1460032262276481753723461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3893419366070618009929229 1460032262276481753723461)
                    ·
                      refine ⟨273756049176840328823149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1460032262276481753723461 273756049176840328823149)
                      ·
                        rfl

theorem cell23_533138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_533138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533138 prefixEnd_533138 := by exact prefixLift 533138
  have htrace : WordTrace (prefixWord ++ tailWord_533138) baseStart_533138 baseEnd_533138 := by
    simpa [prefixWord, tailWord_533138, baseEnd_533138] using wordTrace_append hprefix tailTrace_533138
  have hstable : (prefixWord ++ tailWord_533138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533138).length < 2 ^ (prefixWord ++ tailWord_533138).sum := by decide
  have hdescent : baseEnd_533138 < baseStart_533138 := by decide
  rcases family_descends (prefixWord ++ tailWord_533138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533165 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_533165 : Nat := 118140960795 + 533165 * 2 ^ 59
def prefixEnd_533165 : Nat := 4983230072969 + 3 ^ 40 * 533165 * 2
def baseEnd_533165 : Nat := 91256637718170574395175

theorem tailTrace_533165 : CollatzResearch.WordTrace tailWord_533165 prefixEnd_533165 91256637718170574395175 := by
  unfold tailWord_533165
  simp only [CollatzResearch.WordTrace]
  refine ⟨19446125113441737177664949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12964083408961158118443299 19446125113441737177664949)
  ·
    refine ⟨1823074229385162860406089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19446125113441737177664949 1823074229385162860406089)
    ·
      refine ⟨1367305672038872145304567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1823074229385162860406089 1367305672038872145304567)
      ·
        refine ⟨2050958508058308217956851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367305672038872145304567 2050958508058308217956851)
        ·
          refine ⟨3076437762087462326935277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050958508058308217956851 3076437762087462326935277)
          ·
            refine ⟨1153664160782798372600729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3076437762087462326935277 1153664160782798372600729)
            ·
              refine ⟨865248120587098779450547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153664160782798372600729 865248120587098779450547)
              ·
                refine ⟨1297872180880648169175821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865248120587098779450547 1297872180880648169175821)
                ·
                  refine ⟨486702067830243063440933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1297872180880648169175821 486702067830243063440933)
                  ·
                    refine ⟨91256637718170574395175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 486702067830243063440933 91256637718170574395175)
                    ·
                      rfl

theorem cell23_533165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_533165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533165 prefixEnd_533165 := by exact prefixLift 533165
  have htrace : WordTrace (prefixWord ++ tailWord_533165) baseStart_533165 baseEnd_533165 := by
    simpa [prefixWord, tailWord_533165, baseEnd_533165] using wordTrace_append hprefix tailTrace_533165
  have hstable : (prefixWord ++ tailWord_533165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533165).length < 2 ^ (prefixWord ++ tailWord_533165).sum := by decide
  have hdescent : baseEnd_533165 < baseStart_533165 := by decide
  rcases family_descends (prefixWord ++ tailWord_533165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533178 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_533178 : Nat := 118140960795 + 533178 * 2 ^ 59
def prefixEnd_533178 : Nat := 4983230072969 + 3 ^ 40 * 533178 * 2
def baseEnd_533178 : Nat := 30419620933668908035885

theorem tailTrace_533178 : CollatzResearch.WordTrace tailWord_533178 prefixEnd_533178 30419620933668908035885 := by
  unfold tailWord_533178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861649815598660099472047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12964399508263093598592125 4861649815598660099472047)
  ·
    refine ⟨7292474723397990149208071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4861649815598660099472047 7292474723397990149208071)
    ·
      refine ⟨10938712085096985223812107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7292474723397990149208071 10938712085096985223812107)
      ·
        refine ⟨16408068127645477835718161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10938712085096985223812107 16408068127645477835718161)
        ·
          refine ⟨12306051095734108376788621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16408068127645477835718161 12306051095734108376788621)
          ·
            refine ⟨4614769160900290641295733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12306051095734108376788621 4614769160900290641295733)
            ·
              refine ⟨432634608834402247621475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4614769160900290641295733 432634608834402247621475)
              ·
                refine ⟨648951913251603371432213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432634608834402247621475 648951913251603371432213)
                ·
                  refine ⟨30419620933668908035885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648951913251603371432213 30419620933668908035885)
                  ·
                    rfl

theorem cell23_533178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_533178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533178 prefixEnd_533178 := by exact prefixLift 533178
  have htrace : WordTrace (prefixWord ++ tailWord_533178) baseStart_533178 baseEnd_533178 := by
    simpa [prefixWord, tailWord_533178, baseEnd_533178] using wordTrace_append hprefix tailTrace_533178
  have hstable : (prefixWord ++ tailWord_533178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533178).length < 2 ^ (prefixWord ++ tailWord_533178).sum := by decide
  have hdescent : baseEnd_533178 < baseStart_533178 := by decide
  rcases family_descends (prefixWord ++ tailWord_533178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533208 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_533208 : Nat := 118140960795 + 533208 * 2 ^ 59
def prefixEnd_533208 : Nat := 4983230072969 + 3 ^ 40 * 533208 * 2
def baseEnd_533208 : Nat := 91263997607551684982609

theorem tailTrace_533208 : CollatzResearch.WordTrace tailWord_533208 prefixEnd_533208 91263997607551684982609 := by
  unfold tailWord_533208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723846726142977760740139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12965128968190637014320185 9723846726142977760740139)
  ·
    refine ⟨14585770089214466641110209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723846726142977760740139 14585770089214466641110209)
    ·
      refine ⟨10939327566910849980832657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14585770089214466641110209 10939327566910849980832657)
      ·
        refine ⟨8204495675183137485624493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10939327566910849980832657 8204495675183137485624493)
        ·
          refine ⟨3076685878193676557109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8204495675183137485624493 3076685878193676557109185)
          ·
            refine ⟨2307514408645257417831889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3076685878193676557109185 2307514408645257417831889)
            ·
              refine ⟨1730635806483943063373917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307514408645257417831889 1730635806483943063373917)
              ·
                refine ⟨648988427431478648765219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730635806483943063373917 648988427431478648765219)
                ·
                  refine ⟨973482641147217973147829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648988427431478648765219 973482641147217973147829)
                  ·
                    refine ⟨91263997607551684982609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 973482641147217973147829 91263997607551684982609)
                    ·
                      rfl

theorem cell23_533208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_533208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533208 prefixEnd_533208 := by exact prefixLift 533208
  have htrace : WordTrace (prefixWord ++ tailWord_533208) baseStart_533208 baseEnd_533208 := by
    simpa [prefixWord, tailWord_533208, baseEnd_533208] using wordTrace_append hprefix tailTrace_533208
  have hstable : (prefixWord ++ tailWord_533208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533208).length < 2 ^ (prefixWord ++ tailWord_533208).sum := by decide
  have hdescent : baseEnd_533208 < baseStart_533208 := by decide
  rcases family_descends (prefixWord ++ tailWord_533208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533215 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 2, 3, 2]
def baseStart_533215 : Nat := 118140960795 + 533215 * 2 ^ 59
def prefixEnd_533215 : Nat := 4983230072969 + 3 ^ 40 * 533215 * 2
def baseEnd_533215 : Nat := 273795587187236527560295

theorem tailTrace_533215 : CollatzResearch.WordTrace tailWord_533215 prefixEnd_533215 273795587187236527560295 := by
  unfold tailWord_533215
  simp only [CollatzResearch.WordTrace]
  refine ⟨19447948763260595716985099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12965299175507063811323399 19447948763260595716985099)
  ·
    refine ⟨29171923144890893575477649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19447948763260595716985099 29171923144890893575477649)
    ·
      refine ⟨21878942358668170181608237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29171923144890893575477649 21878942358668170181608237)
      ·
        refine ⟨8204603384500563818103089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21878942358668170181608237 8204603384500563818103089)
        ·
          refine ⟨6153452538375422863577317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8204603384500563818103089 6153452538375422863577317)
          ·
            refine ⟨1153772350945391786920747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6153452538375422863577317 1153772350945391786920747)
            ·
              refine ⟨1730658526418087680381121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153772350945391786920747 1730658526418087680381121)
              ·
                refine ⟨1297993894813565760285841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730658526418087680381121 1297993894813565760285841)
                ·
                  refine ⟨973495421110174320214381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1297993894813565760285841 973495421110174320214381)
                  ·
                    refine ⟨365060782916315370080393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 973495421110174320214381 365060782916315370080393)
                    ·
                      refine ⟨273795587187236527560295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365060782916315370080393 273795587187236527560295)
                      ·
                        rfl

theorem cell23_533215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_533215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533215 prefixEnd_533215 := by exact prefixLift 533215
  have htrace : WordTrace (prefixWord ++ tailWord_533215) baseStart_533215 baseEnd_533215 := by
    simpa [prefixWord, tailWord_533215, baseEnd_533215] using wordTrace_append hprefix tailTrace_533215
  have hstable : (prefixWord ++ tailWord_533215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533215).length < 2 ^ (prefixWord ++ tailWord_533215).sum := by decide
  have hdescent : baseEnd_533215 < baseStart_533215 := by decide
  rcases family_descends (prefixWord ++ tailWord_533215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533238 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_533238 : Nat := 118140960795 + 533238 * 2 ^ 59
def prefixEnd_533238 : Nat := 4983230072969 + 3 ^ 40 * 533238 * 2
def baseEnd_533238 : Nat := 91269132414096645857563

theorem tailTrace_533238 : CollatzResearch.WordTrace tailWord_533238 prefixEnd_533238 91269132414096645857563 := by
  unfold tailWord_533238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215549227636079415317023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12965858428118180430048245 1215549227636079415317023)
  ·
    refine ⟨1823323841454119122975535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215549227636079415317023 1823323841454119122975535)
    ·
      refine ⟨2734985762181178684463303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823323841454119122975535 2734985762181178684463303)
      ·
        refine ⟨4102478643271768026694955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2734985762181178684463303 4102478643271768026694955)
        ·
          refine ⟨6153717964907652040042433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102478643271768026694955 6153717964907652040042433)
          ·
            refine ⟨4615288473680739030031825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153717964907652040042433 4615288473680739030031825)
            ·
              refine ⟨3461466355260554272523869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4615288473680739030031825 3461466355260554272523869)
              ·
                refine ⟨1298049883222707852196451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3461466355260554272523869 1298049883222707852196451)
                ·
                  refine ⟨1947074824834061778294677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298049883222707852196451 1947074824834061778294677)
                  ·
                    refine ⟨91269132414096645857563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1947074824834061778294677 91269132414096645857563)
                    ·
                      rfl

theorem cell23_533238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_533238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533238 prefixEnd_533238 := by exact prefixLift 533238
  have htrace : WordTrace (prefixWord ++ tailWord_533238) baseStart_533238 baseEnd_533238 := by
    simpa [prefixWord, tailWord_533238, baseEnd_533238] using wordTrace_append hprefix tailTrace_533238
  have hstable : (prefixWord ++ tailWord_533238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533238).length < 2 ^ (prefixWord ++ tailWord_533238).sum := by decide
  have hdescent : baseEnd_533238 < baseStart_533238 := by decide
  rcases family_descends (prefixWord ++ tailWord_533238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533241 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_533241 : Nat := 118140960795 + 533241 * 2 ^ 59
def prefixEnd_533241 : Nat := 4983230072969 + 3 ^ 40 * 533241 * 2
def baseEnd_533241 : Nat := 273808937684253425835175

theorem tailTrace_533241 : CollatzResearch.WordTrace tailWord_533241 prefixEnd_533241 273808937684253425835175 := by
  unfold tailWord_533241
  simp only [CollatzResearch.WordTrace]
  refine ⟨19448897061166402157431577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12965931374110934771621051 19448897061166402157431577)
  ·
    refine ⟨14586672795874801618073683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19448897061166402157431577 14586672795874801618073683)
    ·
      refine ⟨21880009193812202427110525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14586672795874801618073683 21880009193812202427110525)
      ·
        refine ⟨8205003447679575910166447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21880009193812202427110525 8205003447679575910166447)
        ·
          refine ⟨12307505171519363865249671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205003447679575910166447 12307505171519363865249671)
          ·
            refine ⟨18461257757279045797874507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12307505171519363865249671 18461257757279045797874507)
            ·
              refine ⟨27691886635918568696811761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18461257757279045797874507 27691886635918568696811761)
              ·
                refine ⟨20768914976938926522608821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27691886635918568696811761 20768914976938926522608821)
                ·
                  refine ⟨1947085779088024361494577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20768914976938926522608821 1947085779088024361494577)
                  ·
                    refine ⟨1460314334316018271120933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947085779088024361494577 1460314334316018271120933)
                    ·
                      refine ⟨273808937684253425835175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1460314334316018271120933 273808937684253425835175)
                      ·
                        rfl

theorem cell23_533241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_533241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533241 prefixEnd_533241 := by exact prefixLift 533241
  have htrace : WordTrace (prefixWord ++ tailWord_533241) baseStart_533241 baseEnd_533241 := by
    simpa [prefixWord, tailWord_533241, baseEnd_533241] using wordTrace_append hprefix tailTrace_533241
  have hstable : (prefixWord ++ tailWord_533241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533241).length < 2 ^ (prefixWord ++ tailWord_533241).sum := by decide
  have hdescent : baseEnd_533241 < baseStart_533241 := by decide
  rcases family_descends (prefixWord ++ tailWord_533241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533245 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_533245 : Nat := 118140960795 + 533245 * 2 ^ 59
def prefixEnd_533245 : Nat := 4983230072969 + 3 ^ 40 * 533245 * 2
def baseEnd_533245 : Nat := 273810991606871410185157

theorem tailTrace_533245 : CollatzResearch.WordTrace tailWord_533245 prefixEnd_533245 273810991606871410185157 := by
  unfold tailWord_533245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19449042953151910840577189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12966028635434607227051459 19449042953151910840577189)
  ·
    refine ⟨3646695553715983282608223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19449042953151910840577189 3646695553715983282608223)
    ·
      refine ⟨5470043330573974923912335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646695553715983282608223 5470043330573974923912335)
      ·
        refine ⟨8205064995860962385868503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5470043330573974923912335 8205064995860962385868503)
        ·
          refine ⟨12307597493791443578802755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205064995860962385868503 12307597493791443578802755)
          ·
            refine ⟨18461396240687165368204133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12307597493791443578802755 18461396240687165368204133)
            ·
              refine ⟨3461511795128843506538275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18461396240687165368204133 3461511795128843506538275)
              ·
                refine ⟨5192267692693265259807413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3461511795128843506538275 5192267692693265259807413)
                ·
                  refine ⟨486775096189993618106945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5192267692693265259807413 486775096189993618106945)
                  ·
                    refine ⟨365081322142495213580209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486775096189993618106945 365081322142495213580209)
                    ·
                      refine ⟨273810991606871410185157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365081322142495213580209 273810991606871410185157)
                      ·
                        rfl

theorem cell23_533245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_533245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533245 prefixEnd_533245 := by exact prefixLift 533245
  have htrace : WordTrace (prefixWord ++ tailWord_533245) baseStart_533245 baseEnd_533245 := by
    simpa [prefixWord, tailWord_533245, baseEnd_533245] using wordTrace_append hprefix tailTrace_533245
  have hstable : (prefixWord ++ tailWord_533245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533245).length < 2 ^ (prefixWord ++ tailWord_533245).sum := by decide
  have hdescent : baseEnd_533245 < baseStart_533245 := by decide
  rcases family_descends (prefixWord ++ tailWord_533245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533258 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_533258 : Nat := 118140960795 + 533258 * 2 ^ 59
def prefixEnd_533258 : Nat := 4983230072969 + 3 ^ 40 * 533258 * 2
def baseEnd_533258 : Nat := 273817666855379859322597

theorem tailTrace_533258 : CollatzResearch.WordTrace tailWord_533258 prefixEnd_533258 273817666855379859322597 := by
  unfold tailWord_533258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4862379275526203515200107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12966344734736542707200285 4862379275526203515200107)
  ·
    refine ⟨7293568913289305272800161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4862379275526203515200107 7293568913289305272800161)
    ·
      refine ⟨5470176684966978954600121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7293568913289305272800161 5470176684966978954600121)
      ·
        refine ⟨4102632513725234215950091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5470176684966978954600121 4102632513725234215950091)
        ·
          refine ⟨6153948770587851323925137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102632513725234215950091 6153948770587851323925137)
          ·
            refine ⟨4615461577940888492943853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153948770587851323925137 4615461577940888492943853)
            ·
              refine ⟨1730798091727833184853945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4615461577940888492943853 1730798091727833184853945)
              ·
                refine ⟨1298098568795874888640459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1730798091727833184853945 1298098568795874888640459)
                ·
                  refine ⟨1947147853193812332960689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298098568795874888640459 1947147853193812332960689)
                  ·
                    refine ⟨1460360889895359249720517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1947147853193812332960689 1460360889895359249720517)
                    ·
                      refine ⟨273817666855379859322597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1460360889895359249720517 273817666855379859322597)
                      ·
                        rfl

theorem cell23_533258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_533258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533258 prefixEnd_533258 := by exact prefixLift 533258
  have htrace : WordTrace (prefixWord ++ tailWord_533258) baseStart_533258 baseEnd_533258 := by
    simpa [prefixWord, tailWord_533258, baseEnd_533258] using wordTrace_append hprefix tailTrace_533258
  have hstable : (prefixWord ++ tailWord_533258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533258).length < 2 ^ (prefixWord ++ tailWord_533258).sum := by decide
  have hdescent : baseEnd_533258 < baseStart_533258 := by decide
  rcases family_descends (prefixWord ++ tailWord_533258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533268 : List Nat := [2, 4, 4, 13]
def baseStart_533268 : Nat := 118140960795 + 533268 * 2 ^ 59
def prefixEnd_533268 : Nat := 4983230072969 + 3 ^ 40 * 533268 * 2
def baseEnd_533268 : Nat := 125204756132567361773

theorem tailTrace_533268 : CollatzResearch.WordTrace tailWord_533268 prefixEnd_533268 125204756132567361773 := by
  unfold tailWord_533268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724940916034292884332229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12966587888045723845776305 9724940916034292884332229)
  ·
    refine ⟨1823426421756429915812293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9724940916034292884332229 1823426421756429915812293)
    ·
      refine ⟨341892454079330609214805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1823426421756429915812293 341892454079330609214805)
      ·
        refine ⟨125204756132567361773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 341892454079330609214805 125204756132567361773)
        ·
          rfl

theorem cell23_533268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 13].length) (baseStart_533268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533268 prefixEnd_533268 := by exact prefixLift 533268
  have htrace : WordTrace (prefixWord ++ tailWord_533268) baseStart_533268 baseEnd_533268 := by
    simpa [prefixWord, tailWord_533268, baseEnd_533268] using wordTrace_append hprefix tailTrace_533268
  have hstable : (prefixWord ++ tailWord_533268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533268).length < 2 ^ (prefixWord ++ tailWord_533268).sum := by decide
  have hdescent : baseEnd_533268 < baseStart_533268 := by decide
  rcases family_descends (prefixWord ++ tailWord_533268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_533279 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 1, 2, 2]
def baseStart_533279 : Nat := 118140960795 + 533279 * 2 ^ 59
def prefixEnd_533279 : Nat := 4983230072969 + 3 ^ 40 * 533279 * 2
def baseEnd_533279 : Nat := 273828449949124277160001

theorem tailTrace_533279 : CollatzResearch.WordTrace tailWord_533279 prefixEnd_533279 273828449949124277160001 := by
  unfold tailWord_533279
  simp only [CollatzResearch.WordTrace]
  refine ⟨19450283035028734647314891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12966855356685823098209927 19450283035028734647314891)
  ·
    refine ⟨29175424552543101970972337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19450283035028734647314891 29175424552543101970972337)
    ·
      refine ⟨21881568414407326478229253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29175424552543101970972337 21881568414407326478229253)
      ·
        refine ⟨4102794077701373714667985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21881568414407326478229253 4102794077701373714667985)
        ·
          refine ⟨3077095558276030286000989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4102794077701373714667985 3077095558276030286000989)
          ·
            refine ⟨1153910834353511357250371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3077095558276030286000989 1153910834353511357250371)
            ·
              refine ⟨1730866251530267035875557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153910834353511357250371 1730866251530267035875557)
              ·
                refine ⟨324537422161925069226667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1730866251530267035875557 324537422161925069226667)
                ·
                  refine ⟨486806133242887603840001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324537422161925069226667 486806133242887603840001)
                  ·
                    refine ⟨365104599932165702880001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486806133242887603840001 365104599932165702880001)
                    ·
                      refine ⟨273828449949124277160001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 365104599932165702880001 273828449949124277160001)
                      ·
                        rfl

theorem cell23_533279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_533279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_533279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_533279 prefixEnd_533279 := by exact prefixLift 533279
  have htrace : WordTrace (prefixWord ++ tailWord_533279) baseStart_533279 baseEnd_533279 := by
    simpa [prefixWord, tailWord_533279, baseEnd_533279] using wordTrace_append hprefix tailTrace_533279
  have hstable : (prefixWord ++ tailWord_533279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_533279).length < 2 ^ (prefixWord ++ tailWord_533279).sum := by decide
  have hdescent : baseEnd_533279 < baseStart_533279 := by decide
  rcases family_descends (prefixWord ++ tailWord_533279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
