import V185TrunkScan23Chunk0113

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_673949 : List Nat := [1, 4, 2, 1, 1, 5, 2, 7]
def baseStart_673949 : Nat := 118140960795 + 673949 * 2 ^ 59
def prefixEnd_673949 : Nat := 4983230072969 + 3 ^ 40 * 673949 * 2
def baseEnd_673949 : Nat := 12817028652484774264373

theorem tailTrace_673949 : CollatzResearch.WordTrace tailWord_673949 prefixEnd_673949 12817028652484774264373 := by
  unfold tailWord_673949
  simp only [CollatzResearch.WordTrace]
  refine ⟨24580939435405349170624901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16387292956936899447083267 24580939435405349170624901)
  ·
    refine ⟨4608926144138502969492169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24580939435405349170624901 4608926144138502969492169)
    ·
      refine ⟨3456694608103877227119127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4608926144138502969492169 3456694608103877227119127)
      ·
        refine ⟨5185041912155815840678691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456694608103877227119127 5185041912155815840678691)
        ·
          refine ⟨7777562868233723761018037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185041912155815840678691 7777562868233723761018037)
          ·
            refine ⟨729146518896911602595441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7777562868233723761018037 729146518896911602595441)
            ·
              refine ⟨546859889172683701946581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729146518896911602595441 546859889172683701946581)
              ·
                refine ⟨12817028652484774264373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 546859889172683701946581 12817028652484774264373)
                ·
                  rfl

theorem cell23_673949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 7].length) (baseStart_673949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673949 prefixEnd_673949 := by exact prefixLift 673949
  have htrace : WordTrace (prefixWord ++ tailWord_673949) baseStart_673949 baseEnd_673949 := by
    simpa [prefixWord, tailWord_673949, baseEnd_673949] using wordTrace_append hprefix tailTrace_673949
  have hstable : (prefixWord ++ tailWord_673949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673949).length < 2 ^ (prefixWord ++ tailWord_673949).sum := by decide
  have hdescent : baseEnd_673949 < baseStart_673949 := by decide
  rcases family_descends (prefixWord ++ tailWord_673949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673966 : List Nat := [4, 1, 4, 2, 1, 2, 9]
def baseStart_673966 : Nat := 118140960795 + 673966 * 2 ^ 59
def prefixEnd_673966 : Nat := 4983230072969 + 3 ^ 40 * 673966 * 2
def baseEnd_673966 : Nat := 4272450651706362205253

theorem tailTrace_673966 : CollatzResearch.WordTrace tailWord_673966 prefixEnd_673966 4272450651706362205253 := by
  unfold tailWord_673966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072694934542970134249219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16387706317562507382662501 3072694934542970134249219)
  ·
    refine ⟨4609042401814455201373829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072694934542970134249219 4609042401814455201373829)
    ·
      refine ⟨864195450340210350257593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4609042401814455201373829 864195450340210350257593)
      ·
        refine ⟨648146587755157762693195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864195450340210350257593 648146587755157762693195)
        ·
          refine ⟨972219881632736644039793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648146587755157762693195 972219881632736644039793)
          ·
            refine ⟨729164911224552483029845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972219881632736644039793 729164911224552483029845)
            ·
              refine ⟨4272450651706362205253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 729164911224552483029845 4272450651706362205253)
              ·
                rfl

theorem cell23_673966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 9].length) (baseStart_673966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673966 prefixEnd_673966 := by exact prefixLift 673966
  have htrace : WordTrace (prefixWord ++ tailWord_673966) baseStart_673966 baseEnd_673966 := by
    simpa [prefixWord, tailWord_673966, baseEnd_673966] using wordTrace_append hprefix tailTrace_673966
  have hstable : (prefixWord ++ tailWord_673966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673966).length < 2 ^ (prefixWord ++ tailWord_673966).sum := by decide
  have hdescent : baseEnd_673966 < baseStart_673966 := by decide
  rcases family_descends (prefixWord ++ tailWord_673966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673999 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 4, 2]
def baseStart_673999 : Nat := 118140960795 + 673999 * 2 ^ 59
def prefixEnd_673999 : Nat := 4983230072969 + 3 ^ 40 * 673999 * 2
def baseEnd_673999 : Nat := 346085447649813709512841

theorem tailTrace_673999 : CollatzResearch.WordTrace tailWord_673999 prefixEnd_673999 346085447649813709512841 := by
  unfold tailWord_673999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24582763085224207709945051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16388508723482805139963367 24582763085224207709945051)
  ·
    refine ⟨36874144627836311564917577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24582763085224207709945051 36874144627836311564917577)
    ·
      refine ⟨27655608470877233673688183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36874144627836311564917577 27655608470877233673688183)
      ·
        refine ⟨41483412706315850510532275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27655608470877233673688183 41483412706315850510532275)
        ·
          refine ⟨62225119059473775765798413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41483412706315850510532275 62225119059473775765798413)
          ·
            refine ⟨23334419647302665912174405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62225119059473775765798413 23334419647302665912174405)
            ·
              refine ⟨4375203683869249858532701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23334419647302665912174405 4375203683869249858532701)
              ·
                refine ⟨1640701381450968696949763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4375203683869249858532701 1640701381450968696949763)
                ·
                  refine ⟨2461052072176453045424645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640701381450968696949763 2461052072176453045424645)
                  ·
                    refine ⟨461447263533084946017121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461052072176453045424645 461447263533084946017121)
                    ·
                      refine ⟨346085447649813709512841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461447263533084946017121 346085447649813709512841)
                      ·
                        rfl

theorem cell23_673999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4, 2].length) (baseStart_673999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_673999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_673999 prefixEnd_673999 := by exact prefixLift 673999
  have htrace : WordTrace (prefixWord ++ tailWord_673999) baseStart_673999 baseEnd_673999 := by
    simpa [prefixWord, tailWord_673999, baseEnd_673999] using wordTrace_append hprefix tailTrace_673999
  have hstable : (prefixWord ++ tailWord_673999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673999).length < 2 ^ (prefixWord ++ tailWord_673999).sum := by decide
  have hdescent : baseEnd_673999 < baseStart_673999 := by decide
  rcases family_descends (prefixWord ++ tailWord_673999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674032 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_674032 : Nat := 118140960795 + 674032 * 2 ^ 59
def prefixEnd_674032 : Nat := 4983230072969 + 3 ^ 40 * 674032 * 2
def baseEnd_674032 : Nat := 346102392511412080400189

theorem tailTrace_674032 : CollatzResearch.WordTrace tailWord_674032 prefixEnd_674032 346102392511412080400189 := by
  unfold tailWord_674032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291983347052327172948175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16389311129403102897264233 12291983347052327172948175)
  ·
    refine ⟨18437975020578490759422263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12291983347052327172948175 18437975020578490759422263)
    ·
      refine ⟨27656962530867736139133395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18437975020578490759422263 27656962530867736139133395)
      ·
        refine ⟨41485443796301604208700093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27656962530867736139133395 41485443796301604208700093)
        ·
          refine ⟨15557041423613101578262535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41485443796301604208700093 15557041423613101578262535)
          ·
            refine ⟨23335562135419652367393803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15557041423613101578262535 23335562135419652367393803)
            ·
              refine ⟨35003343203129478551090705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23335562135419652367393803 35003343203129478551090705)
              ·
                refine ⟨26252507402347108913318029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35003343203129478551090705 26252507402347108913318029)
                ·
                  refine ⟨9844690275880165842494261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26252507402347108913318029 9844690275880165842494261)
                  ·
                    refine ⟨922939713363765547733837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9844690275880165842494261 922939713363765547733837)
                    ·
                      refine ⟨346102392511412080400189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 922939713363765547733837 346102392511412080400189)
                      ·
                        rfl

theorem cell23_674032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_674032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674032 prefixEnd_674032 := by exact prefixLift 674032
  have htrace : WordTrace (prefixWord ++ tailWord_674032) baseStart_674032 baseEnd_674032 := by
    simpa [prefixWord, tailWord_674032, baseEnd_674032] using wordTrace_append hprefix tailTrace_674032
  have hstable : (prefixWord ++ tailWord_674032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674032).length < 2 ^ (prefixWord ++ tailWord_674032).sum := by decide
  have hdescent : baseEnd_674032 < baseStart_674032 := by decide
  rcases family_descends (prefixWord ++ tailWord_674032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674049 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_674049 : Nat := 118140960795 + 674049 * 2 ^ 59
def prefixEnd_674049 : Nat := 4983230072969 + 3 ^ 40 * 674049 * 2
def baseEnd_674049 : Nat := 346111121682538513887611

theorem tailTrace_674049 : CollatzResearch.WordTrace tailWord_674049 prefixEnd_674049 346111121682538513887611 := by
  unfold tailWord_674049
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584586735043066249265201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16389724490028710832843467 24584586735043066249265201)
  ·
    refine ⟨18438440051282299686948901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24584586735043066249265201 18438440051282299686948901)
    ·
      refine ⟨3457207509615431191302919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18438440051282299686948901 3457207509615431191302919)
      ·
        refine ⟨5185811264423146786954379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457207509615431191302919 5185811264423146786954379)
        ·
          refine ⟨7778716896634720180431569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185811264423146786954379 7778716896634720180431569)
          ·
            refine ⟨5834037672476040135323677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7778716896634720180431569 5834037672476040135323677)
            ·
              refine ⟨2187764127178515050746379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5834037672476040135323677 2187764127178515050746379)
              ·
                refine ⟨3281646190767772576119569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187764127178515050746379 3281646190767772576119569)
                ·
                  refine ⟨2461234643075829432089677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3281646190767772576119569 2461234643075829432089677)
                  ·
                    refine ⟨922962991153436037033629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2461234643075829432089677 922962991153436037033629)
                    ·
                      refine ⟨346111121682538513887611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 922962991153436037033629 346111121682538513887611)
                      ·
                        rfl

theorem cell23_674049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_674049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674049 prefixEnd_674049 := by exact prefixLift 674049
  have htrace : WordTrace (prefixWord ++ tailWord_674049) baseStart_674049 baseEnd_674049 := by
    simpa [prefixWord, tailWord_674049, baseEnd_674049] using wordTrace_append hprefix tailTrace_674049
  have hstable : (prefixWord ++ tailWord_674049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674049).length < 2 ^ (prefixWord ++ tailWord_674049).sum := by decide
  have hdescent : baseEnd_674049 < baseStart_674049 := by decide
  rcases family_descends (prefixWord ++ tailWord_674049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674050 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_674050 : Nat := 118140960795 + 674050 * 2 ^ 59
def prefixEnd_674050 : Nat := 4983230072969 + 3 ^ 40 * 674050 * 2
def baseEnd_674050 : Nat := 346111635163193009975107

theorem tailTrace_674050 : CollatzResearch.WordTrace tailWord_674050 prefixEnd_674050 346111635163193009975107 := by
  unfold tailWord_674050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146155802009860855012901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16389748805359628946701069 6146155802009860855012901)
  ·
    refine ⟨1152404212876848910314919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6146155802009860855012901 1152404212876848910314919)
    ·
      refine ⟨1728606319315273365472379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152404212876848910314919 1728606319315273365472379)
      ·
        refine ⟨2592909478972910048208569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728606319315273365472379 2592909478972910048208569)
        ·
          refine ⟨1944682109229682536156427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592909478972910048208569 1944682109229682536156427)
          ·
            refine ⟨2917023163844523804234641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944682109229682536156427 2917023163844523804234641)
            ·
              refine ⟨2187767372883392853175981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917023163844523804234641 2187767372883392853175981)
              ·
                refine ⟨820412764831272319940993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2187767372883392853175981 820412764831272319940993)
                ·
                  refine ⟨615309573623454239955745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820412764831272319940993 615309573623454239955745)
                  ·
                    refine ⟨461482180217590679966809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615309573623454239955745 461482180217590679966809)
                    ·
                      refine ⟨346111635163193009975107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461482180217590679966809 346111635163193009975107)
                      ·
                        rfl

theorem cell23_674050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_674050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674050 prefixEnd_674050 := by exact prefixLift 674050
  have htrace : WordTrace (prefixWord ++ tailWord_674050) baseStart_674050 baseEnd_674050 := by
    simpa [prefixWord, tailWord_674050, baseEnd_674050] using wordTrace_append hprefix tailTrace_674050
  have hstable : (prefixWord ++ tailWord_674050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674050).length < 2 ^ (prefixWord ++ tailWord_674050).sum := by decide
  have hdescent : baseEnd_674050 < baseStart_674050 := by decide
  rcases family_descends (prefixWord ++ tailWord_674050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674059 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 5, 2]
def baseStart_674059 : Nat := 118140960795 + 674059 * 2 ^ 59
def prefixEnd_674059 : Nat := 4983230072969 + 3 ^ 40 * 674059 * 2
def baseEnd_674059 : Nat := 346116256489083474762565

theorem tailTrace_674059 : CollatzResearch.WordTrace tailWord_674059 prefixEnd_674059 346116256489083474762565 := by
  unfold tailWord_674059
  simp only [CollatzResearch.WordTrace]
  refine ⟨24584951465006837957129231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16389967643337891971419487 24584951465006837957129231)
  ·
    refine ⟨36877427197510256935693847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24584951465006837957129231 36877427197510256935693847)
    ·
      refine ⟨55316140796265385403540771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36877427197510256935693847 55316140796265385403540771)
      ·
        refine ⟨82974211194398078105311157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55316140796265385403540771 82974211194398078105311157)
        ·
          refine ⟨7778832299474819822372921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82974211194398078105311157 7778832299474819822372921)
          ·
            refine ⟨5834124224606114866779691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7778832299474819822372921 5834124224606114866779691)
            ·
              refine ⟨8751186336909172300169537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834124224606114866779691 8751186336909172300169537)
              ·
                refine ⟨6563389752681879225127153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8751186336909172300169537 6563389752681879225127153)
                ·
                  refine ⟨4922542314511409418845365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6563389752681879225127153 4922542314511409418845365)
                  ·
                    refine ⟨461488341985444633016753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4922542314511409418845365 461488341985444633016753)
                    ·
                      refine ⟨346116256489083474762565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461488341985444633016753 346116256489083474762565)
                      ·
                        rfl

theorem cell23_674059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5, 2].length) (baseStart_674059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674059 prefixEnd_674059 := by exact prefixLift 674059
  have htrace : WordTrace (prefixWord ++ tailWord_674059) baseStart_674059 baseEnd_674059 := by
    simpa [prefixWord, tailWord_674059, baseEnd_674059] using wordTrace_append hprefix tailTrace_674059
  have hstable : (prefixWord ++ tailWord_674059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674059).length < 2 ^ (prefixWord ++ tailWord_674059).sum := by decide
  have hdescent : baseEnd_674059 < baseStart_674059 := by decide
  rcases family_descends (prefixWord ++ tailWord_674059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674069 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_674069 : Nat := 118140960795 + 674069 * 2 ^ 59
def prefixEnd_674069 : Nat := 4983230072969 + 3 ^ 40 * 674069 * 2
def baseEnd_674069 : Nat := 115373797098542811879173

theorem tailTrace_674069 : CollatzResearch.WordTrace tailWord_674069 prefixEnd_674069 115373797098542811879173 := by
  unfold tailWord_674069
  simp only [CollatzResearch.WordTrace]
  refine ⟨24585316194970609664993261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16390210796647073109995507 24585316194970609664993261)
  ·
    refine ⟨9219493573113978624372473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24585316194970609664993261 9219493573113978624372473)
    ·
      refine ⟨6914620179835483968279355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9219493573113978624372473 6914620179835483968279355)
      ·
        refine ⟨10371930269753225952419033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6914620179835483968279355 10371930269753225952419033)
        ·
          refine ⟨7778947702314919464314275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10371930269753225952419033 7778947702314919464314275)
          ·
            refine ⟨11668421553472379196471413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7778947702314919464314275 11668421553472379196471413)
            ·
              refine ⟨1093914520638035549669195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11668421553472379196471413 1093914520638035549669195)
              ·
                refine ⟨1640871780957053324503793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093914520638035549669195 1640871780957053324503793)
                ·
                  refine ⟨1230653835717789993377845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640871780957053324503793 1230653835717789993377845)
                  ·
                    refine ⟨115373797098542811879173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1230653835717789993377845 115373797098542811879173)
                    ·
                      rfl

theorem cell23_674069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_674069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674069 prefixEnd_674069 := by exact prefixLift 674069
  have htrace : WordTrace (prefixWord ++ tailWord_674069) baseStart_674069 baseEnd_674069 := by
    simpa [prefixWord, tailWord_674069, baseEnd_674069] using wordTrace_append hprefix tailTrace_674069
  have hstable : (prefixWord ++ tailWord_674069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674069).length < 2 ^ (prefixWord ++ tailWord_674069).sum := by decide
  have hdescent : baseEnd_674069 < baseStart_674069 := by decide
  rcases family_descends (prefixWord ++ tailWord_674069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674092 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_674092 : Nat := 118140960795 + 674092 * 2 ^ 59
def prefixEnd_674092 : Nat := 4983230072969 + 3 ^ 40 * 674092 * 2
def baseEnd_674092 : Nat := 346133201350681845649913

theorem tailTrace_674092 : CollatzResearch.WordTrace tailWord_674092 prefixEnd_674092 346133201350681845649913 := by
  unfold tailWord_674092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293077536943642296540265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16390770049258189728720353 12293077536943642296540265)
  ·
    refine ⟨9219808152707731722405199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12293077536943642296540265 9219808152707731722405199)
    ·
      refine ⟨13829712229061597583607799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219808152707731722405199 13829712229061597583607799)
      ·
        refine ⟨20744568343592396375411699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829712229061597583607799 20744568343592396375411699)
        ·
          refine ⟨31116852515388594563117549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20744568343592396375411699 31116852515388594563117549)
          ·
            refine ⟨11668819693270722961169081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31116852515388594563117549 11668819693270722961169081)
            ·
              refine ⟨8751614769953042220876811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11668819693270722961169081 8751614769953042220876811)
              ·
                refine ⟨13127422154929563331315217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8751614769953042220876811 13127422154929563331315217)
                ·
                  refine ⟨9845566616197172498486413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13127422154929563331315217 9845566616197172498486413)
                  ·
                    refine ⟨3692087481073939686932405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9845566616197172498486413 3692087481073939686932405)
                    ·
                      refine ⟨346133201350681845649913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3692087481073939686932405 346133201350681845649913)
                      ·
                        rfl

theorem cell23_674092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_674092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674092 prefixEnd_674092 := by exact prefixLift 674092
  have htrace : WordTrace (prefixWord ++ tailWord_674092) baseStart_674092 baseEnd_674092 := by
    simpa [prefixWord, tailWord_674092, baseEnd_674092] using wordTrace_append hprefix tailTrace_674092
  have hstable : (prefixWord ++ tailWord_674092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674092).length < 2 ^ (prefixWord ++ tailWord_674092).sum := by decide
  have hdescent : baseEnd_674092 < baseStart_674092 := by decide
  rcases family_descends (prefixWord ++ tailWord_674092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674106 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_674106 : Nat := 118140960795 + 674106 * 2 ^ 59
def prefixEnd_674106 : Nat := 4983230072969 + 3 ^ 40 * 674106 * 2
def baseEnd_674106 : Nat := 346140390079844790874849

theorem tailTrace_674106 : CollatzResearch.WordTrace tailWord_674106 prefixEnd_674106 346140390079844790874849 := by
  unfold tailWord_674106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146666423959141246022543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16391110463891043322726781 6146666423959141246022543)
  ·
    refine ⟨9219999635938711869033815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146666423959141246022543 9219999635938711869033815)
    ·
      refine ⟨13829999453908067803550723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219999635938711869033815 13829999453908067803550723)
      ·
        refine ⟨20744999180862101705326085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829999453908067803550723 20744999180862101705326085)
        ·
          refine ⟨3889687346411644069748641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20744999180862101705326085 3889687346411644069748641)
          ·
            refine ⟨2917265509808733052311481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3889687346411644069748641 2917265509808733052311481)
            ·
              refine ⟨2187949132356549789233611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2917265509808733052311481 2187949132356549789233611)
              ·
                refine ⟨3281923698534824683850417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187949132356549789233611 3281923698534824683850417)
                ·
                  refine ⟨2461442773901118512887813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3281923698534824683850417 2461442773901118512887813)
                  ·
                    refine ⟨461520520106459721166465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2461442773901118512887813 461520520106459721166465)
                    ·
                      refine ⟨346140390079844790874849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461520520106459721166465 346140390079844790874849)
                      ·
                        rfl

theorem cell23_674106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_674106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674106 prefixEnd_674106 := by exact prefixLift 674106
  have htrace : WordTrace (prefixWord ++ tailWord_674106) baseStart_674106 baseEnd_674106 := by
    simpa [prefixWord, tailWord_674106, baseEnd_674106] using wordTrace_append hprefix tailTrace_674106
  have hstable : (prefixWord ++ tailWord_674106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674106).length < 2 ^ (prefixWord ++ tailWord_674106).sum := by decide
  have hdescent : baseEnd_674106 < baseStart_674106 := by decide
  rcases family_descends (prefixWord ++ tailWord_674106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674122 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_674122 : Nat := 118140960795 + 674122 * 2 ^ 59
def prefixEnd_674122 : Nat := 4983230072969 + 3 ^ 40 * 674122 * 2
def baseEnd_674122 : Nat := 346148605770316728274775

theorem tailTrace_674122 : CollatzResearch.WordTrace tailWord_674122 prefixEnd_674122 346148605770316728274775 := by
  unfold tailWord_674122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146812315944649929168155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16391499509185733144448413 6146812315944649929168155)
  ·
    refine ⟨9220218473916974893752233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146812315944649929168155 9220218473916974893752233)
    ·
      refine ⟨6915163855437731170314175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9220218473916974893752233 6915163855437731170314175)
      ·
        refine ⟨10372745783156596755471263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6915163855437731170314175 10372745783156596755471263)
        ·
          refine ⟨15559118674734895133206895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10372745783156596755471263 15559118674734895133206895)
          ·
            refine ⟨23338678012102342699810343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15559118674734895133206895 23338678012102342699810343)
            ·
              refine ⟨35008017018153514049715515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23338678012102342699810343 35008017018153514049715515)
              ·
                refine ⟨52512025527230271074573273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35008017018153514049715515 52512025527230271074573273)
                ·
                  refine ⟨39384019145422703305929955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52512025527230271074573273 39384019145422703305929955)
                  ·
                    refine ⟨59076028718134054958894933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39384019145422703305929955 59076028718134054958894933)
                    ·
                      refine ⟨346148605770316728274775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 59076028718134054958894933 346148605770316728274775)
                      ·
                        rfl

theorem cell23_674122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_674122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674122 prefixEnd_674122 := by exact prefixLift 674122
  have htrace : WordTrace (prefixWord ++ tailWord_674122) baseStart_674122 baseEnd_674122 := by
    simpa [prefixWord, tailWord_674122, baseEnd_674122] using wordTrace_append hprefix tailTrace_674122
  have hstable : (prefixWord ++ tailWord_674122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674122).length < 2 ^ (prefixWord ++ tailWord_674122).sum := by decide
  have hdescent : baseEnd_674122 < baseStart_674122 := by decide
  rcases family_descends (prefixWord ++ tailWord_674122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674183 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_674183 : Nat := 118140960795 + 674183 * 2 ^ 59
def prefixEnd_674183 : Nat := 4983230072969 + 3 ^ 40 * 674183 * 2
def baseEnd_674183 : Nat := 346179928090240989611995

theorem tailTrace_674183 : CollatzResearch.WordTrace tailWord_674183 prefixEnd_674183 346179928090240989611995 := by
  unfold tailWord_674183
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589474116557607134643203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16392982744371738089762135 24589474116557607134643203)
  ·
    refine ⟨36884211174836410701964805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24589474116557607134643203 36884211174836410701964805)
    ·
      refine ⟨6915789595281827006618401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36884211174836410701964805 6915789595281827006618401)
      ·
        refine ⟨5186842196461370254963801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6915789595281827006618401 5186842196461370254963801)
        ·
          refine ⟨3890131647346027691222851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5186842196461370254963801 3890131647346027691222851)
          ·
            refine ⟨5835197471019041536834277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890131647346027691222851 5835197471019041536834277)
            ·
              refine ⟨1094099525816070288156427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5835197471019041536834277 1094099525816070288156427)
              ·
                refine ⟨1641149288724105432234641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094099525816070288156427 1641149288724105432234641)
                ·
                  refine ⟨1230861966543079074175981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1641149288724105432234641 1230861966543079074175981)
                  ·
                    refine ⟨461573237453654652815993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1230861966543079074175981 461573237453654652815993)
                    ·
                      refine ⟨346179928090240989611995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461573237453654652815993 346179928090240989611995)
                      ·
                        rfl

theorem cell23_674183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_674183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674183 prefixEnd_674183 := by exact prefixLift 674183
  have htrace : WordTrace (prefixWord ++ tailWord_674183) baseStart_674183 baseEnd_674183 := by
    simpa [prefixWord, tailWord_674183, baseEnd_674183] using wordTrace_append hprefix tailTrace_674183
  have hstable : (prefixWord ++ tailWord_674183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674183).length < 2 ^ (prefixWord ++ tailWord_674183).sum := by decide
  have hdescent : baseEnd_674183 < baseStart_674183 := by decide
  rcases family_descends (prefixWord ++ tailWord_674183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674213 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_674213 : Nat := 118140960795 + 674213 * 2 ^ 59
def prefixEnd_674213 : Nat := 4983230072969 + 3 ^ 40 * 674213 * 2
def baseEnd_674213 : Nat := 346195332509875872236857

theorem tailTrace_674213 : CollatzResearch.WordTrace tailWord_674213 prefixEnd_674213 346195332509875872236857 := by
  unfold tailWord_674213
  simp only [CollatzResearch.WordTrace]
  refine ⟨24590568306448922258235293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16393712204299281505490195 24590568306448922258235293)
  ·
    refine ⟨9221463114918345846838235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24590568306448922258235293 9221463114918345846838235)
    ·
      refine ⟨13832194672377518770257353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9221463114918345846838235 13832194672377518770257353)
      ·
        refine ⟨10374146004283139077693015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13832194672377518770257353 10374146004283139077693015)
        ·
          refine ⟨15561219006424708616539523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374146004283139077693015 15561219006424708616539523)
          ·
            refine ⟨23341828509637062924809285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561219006424708616539523 23341828509637062924809285)
            ·
              refine ⟨4376592845556949298401741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23341828509637062924809285 4376592845556949298401741)
              ·
                refine ⟨1641222317083855986900653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4376592845556949298401741 1641222317083855986900653)
                ·
                  refine ⟨615458368906445995087745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1641222317083855986900653 615458368906445995087745)
                  ·
                    refine ⟨461593776679834496315809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615458368906445995087745 461593776679834496315809)
                    ·
                      refine ⟨346195332509875872236857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461593776679834496315809 346195332509875872236857)
                      ·
                        rfl

theorem cell23_674213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_674213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674213 prefixEnd_674213 := by exact prefixLift 674213
  have htrace : WordTrace (prefixWord ++ tailWord_674213) baseStart_674213 baseEnd_674213 := by
    simpa [prefixWord, tailWord_674213, baseEnd_674213] using wordTrace_append hprefix tailTrace_674213
  have hstable : (prefixWord ++ tailWord_674213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674213).length < 2 ^ (prefixWord ++ tailWord_674213).sum := by decide
  have hdescent : baseEnd_674213 < baseStart_674213 := by decide
  rcases family_descends (prefixWord ++ tailWord_674213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674226 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_674226 : Nat := 118140960795 + 674226 * 2 ^ 59
def prefixEnd_674226 : Nat := 4983230072969 + 3 ^ 40 * 674226 * 2
def baseEnd_674226 : Nat := 346202007758384321374297

theorem tailTrace_674226 : CollatzResearch.WordTrace tailWord_674226 prefixEnd_674226 346202007758384321374297 := by
  unfold tailWord_674226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6147760613850456369614633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16394028303601216985639021 6147760613850456369614633)
  ·
    refine ⟨4610820460387842277210975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6147760613850456369614633 4610820460387842277210975)
    ·
      refine ⟨6916230690581763415816463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610820460387842277210975 6916230690581763415816463)
      ·
        refine ⟨10374346035872645123724695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916230690581763415816463 10374346035872645123724695)
        ·
          refine ⟨15561519053808967685587043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374346035872645123724695 15561519053808967685587043)
          ·
            refine ⟨23342278580713451528380565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15561519053808967685587043 23342278580713451528380565)
            ·
              refine ⟨1094169308470943040392839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23342278580713451528380565 1094169308470943040392839)
              ·
                refine ⟨1641253962706414560589259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094169308470943040392839 1641253962706414560589259)
                ·
                  refine ⟨2461880944059621840883889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641253962706414560589259 2461880944059621840883889)
                  ·
                    refine ⟨1846410708044716380662917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2461880944059621840883889 1846410708044716380662917)
                    ·
                      refine ⟨346202007758384321374297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1846410708044716380662917 346202007758384321374297)
                      ·
                        rfl

theorem cell23_674226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_674226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674226 prefixEnd_674226 := by exact prefixLift 674226
  have htrace : WordTrace (prefixWord ++ tailWord_674226) baseStart_674226 baseEnd_674226 := by
    simpa [prefixWord, tailWord_674226, baseEnd_674226] using wordTrace_append hprefix tailTrace_674226
  have hstable : (prefixWord ++ tailWord_674226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674226).length < 2 ^ (prefixWord ++ tailWord_674226).sum := by decide
  have hdescent : baseEnd_674226 < baseStart_674226 := by decide
  rcases family_descends (prefixWord ++ tailWord_674226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674241 : List Nat := [1, 2, 7, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_674241 : Nat := 118140960795 + 674241 * 2 ^ 59
def prefixEnd_674241 : Nat := 4983230072969 + 3 ^ 40 * 674241 * 2
def baseEnd_674241 : Nat := 346209709968201762686729

theorem tailTrace_674241 : CollatzResearch.WordTrace tailWord_674241 prefixEnd_674241 346209709968201762686729 := by
  unfold tailWord_674241
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591589550347483040254577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16394393033564988693503051 24591589550347483040254577)
  ·
    refine ⟨18443692162760612280190933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24591589550347483040254577 18443692162760612280190933)
    ·
      refine ⟨432274035064701850316975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18443692162760612280190933 432274035064701850316975)
      ·
        refine ⟨648411052597052775475463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432274035064701850316975 648411052597052775475463)
        ·
          refine ⟨972616578895579163213195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648411052597052775475463 972616578895579163213195)
          ·
            refine ⟨1458924868343368744819793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972616578895579163213195 1458924868343368744819793)
            ·
              refine ⟨1094193651257526558614845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458924868343368744819793 1094193651257526558614845)
              ·
                refine ⟨410322619221572459480567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094193651257526558614845 410322619221572459480567)
                ·
                  refine ⟨615483928832358689220851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410322619221572459480567 615483928832358689220851)
                  ·
                    refine ⟨923225893248538033831277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 615483928832358689220851 923225893248538033831277)
                    ·
                      refine ⟨346209709968201762686729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923225893248538033831277 346209709968201762686729)
                      ·
                        rfl

theorem cell23_674241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_674241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674241 prefixEnd_674241 := by exact prefixLift 674241
  have htrace : WordTrace (prefixWord ++ tailWord_674241) baseStart_674241 baseEnd_674241 := by
    simpa [prefixWord, tailWord_674241, baseEnd_674241] using wordTrace_append hprefix tailTrace_674241
  have hstable : (prefixWord ++ tailWord_674241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674241).length < 2 ^ (prefixWord ++ tailWord_674241).sum := by decide
  have hdescent : baseEnd_674241 < baseStart_674241 := by decide
  rcases family_descends (prefixWord ++ tailWord_674241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674247 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_674247 : Nat := 118140960795 + 674247 * 2 ^ 59
def prefixEnd_674247 : Nat := 4983230072969 + 3 ^ 40 * 674247 * 2
def baseEnd_674247 : Nat := 346212790852128739211701

theorem tailTrace_674247 : CollatzResearch.WordTrace tailWord_674247 prefixEnd_674247 346212790852128739211701 := by
  unfold tailWord_674247
  simp only [CollatzResearch.WordTrace]
  refine ⟨24591808388325746064972995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16394538925550497376648663 24591808388325746064972995)
  ·
    refine ⟨36887712582488619097459493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24591808388325746064972995 36887712582488619097459493)
    ·
      refine ⟨6916446109216616080773655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36887712582488619097459493 6916446109216616080773655)
      ·
        refine ⟨10374669163824924121160483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6916446109216616080773655 10374669163824924121160483)
        ·
          refine ⟨15562003745737386181740725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374669163824924121160483 15562003745737386181740725)
          ·
            refine ⟨1458937851162879954538193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15562003745737386181740725 1458937851162879954538193)
            ·
              refine ⟨1094203388372159965903645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458937851162879954538193 1094203388372159965903645)
              ·
                refine ⟨410326270639559987213867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094203388372159965903645 410326270639559987213867)
                ·
                  refine ⟨615489405959339980820801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410326270639559987213867 615489405959339980820801)
                  ·
                    refine ⟨461617054469504985615601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615489405959339980820801 461617054469504985615601)
                    ·
                      refine ⟨346212790852128739211701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461617054469504985615601 346212790852128739211701)
                      ·
                        rfl

theorem cell23_674247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_674247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674247 prefixEnd_674247 := by exact prefixLift 674247
  have htrace : WordTrace (prefixWord ++ tailWord_674247) baseStart_674247 baseEnd_674247 := by
    simpa [prefixWord, tailWord_674247, baseEnd_674247] using wordTrace_append hprefix tailTrace_674247
  have hstable : (prefixWord ++ tailWord_674247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674247).length < 2 ^ (prefixWord ++ tailWord_674247).sum := by decide
  have hdescent : baseEnd_674247 < baseStart_674247 := by decide
  rcases family_descends (prefixWord ++ tailWord_674247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674274 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_674274 : Nat := 118140960795 + 674274 * 2 ^ 59
def prefixEnd_674274 : Nat := 4983230072969 + 3 ^ 40 * 674274 * 2
def baseEnd_674274 : Nat := 115408884943266711191359

theorem tailTrace_674274 : CollatzResearch.WordTrace tailWord_674274 prefixEnd_674274 115408884943266711191359 := by
  unfold tailWord_674274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148198289806982419051469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16395195439485286450803917 6148198289806982419051469)
  ·
    refine ⟨2305574358677618407144301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6148198289806982419051469 2305574358677618407144301)
    ·
      refine ⟨864590384504106902679113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2305574358677618407144301 864590384504106902679113)
      ·
        refine ⟨648442788378080177009335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864590384504106902679113 648442788378080177009335)
        ·
          refine ⟨972664182567120265514003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648442788378080177009335 972664182567120265514003)
          ·
            refine ⟨1458996273850680398271005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972664182567120265514003 1458996273850680398271005)
            ·
              refine ⟨547123602694005149351627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458996273850680398271005 547123602694005149351627)
              ·
                refine ⟨820685404041007724027441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547123602694005149351627 820685404041007724027441)
                ·
                  refine ⟨615514053030755793020581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820685404041007724027441 615514053030755793020581)
                  ·
                    refine ⟨115408884943266711191359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615514053030755793020581 115408884943266711191359)
                    ·
                      rfl

theorem cell23_674274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_674274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674274 prefixEnd_674274 := by exact prefixLift 674274
  have htrace : WordTrace (prefixWord ++ tailWord_674274) baseStart_674274 baseEnd_674274 := by
    simpa [prefixWord, tailWord_674274, baseEnd_674274] using wordTrace_append hprefix tailTrace_674274
  have hstable : (prefixWord ++ tailWord_674274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674274).length < 2 ^ (prefixWord ++ tailWord_674274).sum := by decide
  have hdescent : baseEnd_674274 < baseStart_674274 := by decide
  rcases family_descends (prefixWord ++ tailWord_674274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674303 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 6, 2, 2]
def baseStart_674303 : Nat := 118140960795 + 674303 * 2 ^ 59
def prefixEnd_674303 : Nat := 4983230072969 + 3 ^ 40 * 674303 * 2
def baseEnd_674303 : Nat := 346241545768780520111443

theorem tailTrace_674303 : CollatzResearch.WordTrace tailWord_674303 prefixEnd_674303 346241545768780520111443 := by
  unfold tailWord_674303
  simp only [CollatzResearch.WordTrace]
  refine ⟨24593850876122867629011563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16395900584081911752674375 24593850876122867629011563)
  ·
    refine ⟨36890776314184301443517345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24593850876122867629011563 36890776314184301443517345)
    ·
      refine ⟨27668082235638226082638009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36890776314184301443517345 27668082235638226082638009)
      ·
        refine ⟨20751061676728669561978507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27668082235638226082638009 20751061676728669561978507)
        ·
          refine ⟨31126592515093004342967761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20751061676728669561978507 31126592515093004342967761)
          ·
            refine ⟨23344944386319753257225821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31126592515093004342967761 23344944386319753257225821)
            ·
              refine ⟨8754354144869907471459683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23344944386319753257225821 8754354144869907471459683)
              ·
                refine ⟨13131531217304861207189525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8754354144869907471459683 13131531217304861207189525)
                ·
                  refine ⟨615540525811165369087009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13131531217304861207189525 615540525811165369087009)
                  ·
                    refine ⟨461655394358374026815257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615540525811165369087009 461655394358374026815257)
                    ·
                      refine ⟨346241545768780520111443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461655394358374026815257 346241545768780520111443)
                      ·
                        rfl

theorem cell23_674303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_674303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674303 prefixEnd_674303 := by exact prefixLift 674303
  have htrace : WordTrace (prefixWord ++ tailWord_674303) baseStart_674303 baseEnd_674303 := by
    simpa [prefixWord, tailWord_674303, baseEnd_674303] using wordTrace_append hprefix tailTrace_674303
  have hstable : (prefixWord ++ tailWord_674303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674303).length < 2 ^ (prefixWord ++ tailWord_674303).sum := by decide
  have hdescent : baseEnd_674303 < baseStart_674303 := by decide
  rcases family_descends (prefixWord ++ tailWord_674303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674309 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 9]
def baseStart_674309 : Nat := 118140960795 + 674309 * 2 ^ 59
def prefixEnd_674309 : Nat := 4983230072969 + 3 ^ 40 * 674309 * 2
def baseEnd_674309 : Nat := 38471625183634166292935

theorem tailTrace_674309 : CollatzResearch.WordTrace tailWord_674309 prefixEnd_674309 38471625183634166292935 := by
  unfold tailWord_674309
  simp only [CollatzResearch.WordTrace]
  refine ⟨24594069714101130653729981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16396046476067420435819987 24594069714101130653729981)
  ·
    refine ⟨9222776142787923995148743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24594069714101130653729981 9222776142787923995148743)
    ·
      refine ⟨13834164214181885992723115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9222776142787923995148743 13834164214181885992723115)
      ·
        refine ⟨20751246321272828989084673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13834164214181885992723115 20751246321272828989084673)
        ·
          refine ⟨15563434740954621741813505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20751246321272828989084673 15563434740954621741813505)
          ·
            refine ⟨11672576055715966306360129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15563434740954621741813505 11672576055715966306360129)
            ·
              refine ⟨8754432041786974729770097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11672576055715966306360129 8754432041786974729770097)
              ·
                refine ⟨6565824031340231047327573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8754432041786974729770097 6565824031340231047327573)
                ·
                  refine ⟨38471625183634166292935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6565824031340231047327573 38471625183634166292935)
                  ·
                    rfl

theorem cell23_674309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_674309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674309 prefixEnd_674309 := by exact prefixLift 674309
  have htrace : WordTrace (prefixWord ++ tailWord_674309) baseStart_674309 baseEnd_674309 := by
    simpa [prefixWord, tailWord_674309, baseEnd_674309] using wordTrace_append hprefix tailTrace_674309
  have hstable : (prefixWord ++ tailWord_674309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674309).length < 2 ^ (prefixWord ++ tailWord_674309).sum := by decide
  have hdescent : baseEnd_674309 < baseStart_674309 := by decide
  rcases family_descends (prefixWord ++ tailWord_674309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674403 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 3, 4]
def baseStart_674403 : Nat := 118140960795 + 674403 * 2 ^ 59
def prefixEnd_674403 : Nat := 4983230072969 + 3 ^ 40 * 674403 * 2
def baseEnd_674403 : Nat := 115430964611410042953661

theorem tailTrace_674403 : CollatzResearch.WordTrace tailWord_674403 prefixEnd_674403 115430964611410042953661 := by
  unfold tailWord_674403
  simp only [CollatzResearch.WordTrace]
  refine ⟨24597498175760584707651863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16398332117173723138434575 24597498175760584707651863)
  ·
    refine ⟨36896247263640877061477795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24597498175760584707651863 36896247263640877061477795)
    ·
      refine ⟨55344370895461315592216693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36896247263640877061477795 55344370895461315592216693)
      ·
        refine ⟨5188534771449498336770315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55344370895461315592216693 5188534771449498336770315)
        ·
          refine ⟨7782802157174247505155473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5188534771449498336770315 7782802157174247505155473)
          ·
            refine ⟨5837101617880685628866605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7782802157174247505155473 5837101617880685628866605)
            ·
              refine ⟨2188913106705257110824977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5837101617880685628866605 2188913106705257110824977)
              ·
                refine ⟨1641684830028942833118733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188913106705257110824977 1641684830028942833118733)
                ·
                  refine ⟨615631811260853562419525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1641684830028942833118733 615631811260853562419525)
                  ·
                    refine ⟨115430964611410042953661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615631811260853562419525 115430964611410042953661)
                    ·
                      rfl

theorem cell23_674403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 4].length) (baseStart_674403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674403 prefixEnd_674403 := by exact prefixLift 674403
  have htrace : WordTrace (prefixWord ++ tailWord_674403) baseStart_674403 baseEnd_674403 := by
    simpa [prefixWord, tailWord_674403, baseEnd_674403] using wordTrace_append hprefix tailTrace_674403
  have hstable : (prefixWord ++ tailWord_674403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674403).length < 2 ^ (prefixWord ++ tailWord_674403).sum := by decide
  have hdescent : baseEnd_674403 < baseStart_674403 := by decide
  rcases family_descends (prefixWord ++ tailWord_674403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674471 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 1, 4]
def baseStart_674471 : Nat := 118140960795 + 674471 * 2 ^ 59
def prefixEnd_674471 : Nat := 4983230072969 + 3 ^ 40 * 674471 * 2
def baseEnd_674471 : Nat := 115442603506245287603557

theorem tailTrace_674471 : CollatzResearch.WordTrace tailWord_674471 prefixEnd_674471 115442603506245287603557 := by
  unfold tailWord_674471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599978339514232321127267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16399985559676154880751511 24599978339514232321127267)
  ·
    refine ⟨36899967509271348481690901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24599978339514232321127267 36899967509271348481690901)
    ·
      refine ⟨1729685976997094460079261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36899967509271348481690901 1729685976997094460079261)
      ·
        refine ⟨648632241373910422529723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1729685976997094460079261 648632241373910422529723)
        ·
          refine ⟨972948362060865633794585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648632241373910422529723 972948362060865633794585)
          ·
            refine ⟨729711271545649225345939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972948362060865633794585 729711271545649225345939)
            ·
              refine ⟨1094566907318473838018909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729711271545649225345939 1094566907318473838018909)
              ·
                refine ⟨410462590244427689257091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094566907318473838018909 410462590244427689257091)
                ·
                  refine ⟨615693885366641533885637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410462590244427689257091 615693885366641533885637)
                  ·
                    refine ⟨115442603506245287603557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615693885366641533885637 115442603506245287603557)
                    ·
                      rfl

theorem cell23_674471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_674471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674471 prefixEnd_674471 := by exact prefixLift 674471
  have htrace : WordTrace (prefixWord ++ tailWord_674471) baseStart_674471 baseEnd_674471 := by
    simpa [prefixWord, tailWord_674471, baseEnd_674471] using wordTrace_append hprefix tailTrace_674471
  have hstable : (prefixWord ++ tailWord_674471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674471).length < 2 ^ (prefixWord ++ tailWord_674471).sum := by decide
  have hdescent : baseEnd_674471 < baseStart_674471 := by decide
  rcases family_descends (prefixWord ++ tailWord_674471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674487 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_674487 : Nat := 118140960795 + 674487 * 2 ^ 59
def prefixEnd_674487 : Nat := 4983230072969 + 3 ^ 40 * 674487 * 2
def baseEnd_674487 : Nat := 346336026209207800210597

theorem tailTrace_674487 : CollatzResearch.WordTrace tailWord_674487 prefixEnd_674487 346336026209207800210597 := by
  unfold tailWord_674487
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600561907456267053709715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16400374604970844702473143 24600561907456267053709715)
  ·
    refine ⟨36900842861184400580564573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24600561907456267053709715 36900842861184400580564573)
    ·
      refine ⟨13837816072944150217711715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36900842861184400580564573 13837816072944150217711715)
      ·
        refine ⟨20756724109416225326567573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13837816072944150217711715 20756724109416225326567573)
        ·
          refine ⟨972971442628885562182855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20756724109416225326567573 972971442628885562182855)
          ·
            refine ⟨1459457163943328343274283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972971442628885562182855 1459457163943328343274283)
            ·
              refine ⟨2189185745914992514911425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459457163943328343274283 2189185745914992514911425)
              ·
                refine ⟨1641889309436244386183569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189185745914992514911425 1641889309436244386183569)
                ·
                  refine ⟨1231416982077183289637677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1641889309436244386183569 1231416982077183289637677)
                  ·
                    refine ⟨461781368278943733614129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231416982077183289637677 461781368278943733614129)
                    ·
                      refine ⟨346336026209207800210597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461781368278943733614129 346336026209207800210597)
                      ·
                        rfl

theorem cell23_674487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_674487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674487 prefixEnd_674487 := by exact prefixLift 674487
  have htrace : WordTrace (prefixWord ++ tailWord_674487) baseStart_674487 baseEnd_674487 := by
    simpa [prefixWord, tailWord_674487, baseEnd_674487] using wordTrace_append hprefix tailTrace_674487
  have hstable : (prefixWord ++ tailWord_674487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674487).length < 2 ^ (prefixWord ++ tailWord_674487).sum := by decide
  have hdescent : baseEnd_674487 < baseStart_674487 := by decide
  rcases family_descends (prefixWord ++ tailWord_674487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674513 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_674513 : Nat := 118140960795 + 674513 * 2 ^ 59
def prefixEnd_674513 : Nat := 4983230072969 + 3 ^ 40 * 674513 * 2
def baseEnd_674513 : Nat := 346349376706224698485477

theorem tailTrace_674513 : CollatzResearch.WordTrace tailWord_674513 prefixEnd_674513 346349376706224698485477 := by
  unfold tailWord_674513
  simp only [CollatzResearch.WordTrace]
  refine ⟨24601510205362073494156193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16401006803574715662770795 24601510205362073494156193)
  ·
    refine ⟨18451132654021555120617145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24601510205362073494156193 18451132654021555120617145)
    ·
      refine ⟨13838349490516166340462859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18451132654021555120617145 13838349490516166340462859)
      ·
        refine ⟨20757524235774249510694289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838349490516166340462859 20757524235774249510694289)
        ·
          refine ⟨15568143176830687133020717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20757524235774249510694289 15568143176830687133020717)
          ·
            refine ⟨5838053691311507674882769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15568143176830687133020717 5838053691311507674882769)
            ·
              refine ⟨4378540268483630756162077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838053691311507674882769 4378540268483630756162077)
              ·
                refine ⟨1641952600681361533560779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4378540268483630756162077 1641952600681361533560779)
                ·
                  refine ⟨2462928901022042300341169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641952600681361533560779 2462928901022042300341169)
                  ·
                    refine ⟨1847196675766531725255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2462928901022042300341169 1847196675766531725255877)
                    ·
                      refine ⟨346349376706224698485477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1847196675766531725255877 346349376706224698485477)
                      ·
                        rfl

theorem cell23_674513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_674513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674513 prefixEnd_674513 := by exact prefixLift 674513
  have htrace : WordTrace (prefixWord ++ tailWord_674513) baseStart_674513 baseEnd_674513 := by
    simpa [prefixWord, tailWord_674513, baseEnd_674513] using wordTrace_append hprefix tailTrace_674513
  have hstable : (prefixWord ++ tailWord_674513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674513).length < 2 ^ (prefixWord ++ tailWord_674513).sum := by decide
  have hdescent : baseEnd_674513 < baseStart_674513 := by decide
  rcases family_descends (prefixWord ++ tailWord_674513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674514 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_674514 : Nat := 118140960795 + 674514 * 2 ^ 59
def prefixEnd_674514 : Nat := 4983230072969 + 3 ^ 40 * 674514 * 2
def baseEnd_674514 : Nat := 115449963395626398190991

theorem tailTrace_674514 : CollatzResearch.WordTrace tailWord_674514 prefixEnd_674514 115449963395626398190991 := by
  unfold tailWord_674514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6150386669589612666235649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16401031118905633776628397 6150386669589612666235649)
  ·
    refine ⟨4612790002192209499676737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6150386669589612666235649 4612790002192209499676737)
    ·
      refine ⟨3459592501644157124757553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4612790002192209499676737 3459592501644157124757553)
      ·
        refine ⟨2594694376233117843568165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459592501644157124757553 2594694376233117843568165)
        ·
          refine ⟨486505195543709595669031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2594694376233117843568165 486505195543709595669031)
          ·
            refine ⟨729757793315564393503547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486505195543709595669031 729757793315564393503547)
            ·
              refine ⟨1094636689973346590255321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729757793315564393503547 1094636689973346590255321)
              ·
                refine ⟨820977517480009942691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094636689973346590255321 820977517480009942691491)
                ·
                  refine ⟨1231466276220014914037237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820977517480009942691491 1231466276220014914037237)
                  ·
                    refine ⟨115449963395626398190991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1231466276220014914037237 115449963395626398190991)
                    ·
                      rfl

theorem cell23_674514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_674514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674514 prefixEnd_674514 := by exact prefixLift 674514
  have htrace : WordTrace (prefixWord ++ tailWord_674514) baseStart_674514 baseEnd_674514 := by
    simpa [prefixWord, tailWord_674514, baseEnd_674514] using wordTrace_append hprefix tailTrace_674514
  have hstable : (prefixWord ++ tailWord_674514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674514).length < 2 ^ (prefixWord ++ tailWord_674514).sum := by decide
  have hdescent : baseEnd_674514 < baseStart_674514 := by decide
  rcases family_descends (prefixWord ++ tailWord_674514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674517 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_674517 : Nat := 118140960795 + 674517 * 2 ^ 59
def prefixEnd_674517 : Nat := 4983230072969 + 3 ^ 40 * 674517 * 2
def baseEnd_674517 : Nat := 346351430628842682835459

theorem tailTrace_674517 : CollatzResearch.WordTrace tailWord_674517 prefixEnd_674517 346351430628842682835459 := by
  unfold tailWord_674517
  simp only [CollatzResearch.WordTrace]
  refine ⟨24601656097347582177301805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16401104064898388118201203 24601656097347582177301805)
  ·
    refine ⟨9225621036505343316488177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24601656097347582177301805 9225621036505343316488177)
    ·
      refine ⟨6919215777379007487366133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9225621036505343316488177 6919215777379007487366133)
      ·
        refine ⟨648676479129281951940575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6919215777379007487366133 648676479129281951940575)
        ·
          refine ⟨973014718693922927910863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648676479129281951940575 973014718693922927910863)
          ·
            refine ⟨1459522078040884391866295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973014718693922927910863 1459522078040884391866295)
            ·
              refine ⟨2189283117061326587799443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459522078040884391866295 2189283117061326587799443)
              ·
                refine ⟨3283924675591989881699165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189283117061326587799443 3283924675591989881699165)
                ·
                  refine ⟨1231471753346996205637187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3283924675591989881699165 1231471753346996205637187)
                  ·
                    refine ⟨1847207630020494308455781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231471753346996205637187 1847207630020494308455781)
                    ·
                      refine ⟨346351430628842682835459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1847207630020494308455781 346351430628842682835459)
                      ·
                        rfl

theorem cell23_674517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_674517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674517 prefixEnd_674517 := by exact prefixLift 674517
  have htrace : WordTrace (prefixWord ++ tailWord_674517) baseStart_674517 baseEnd_674517 := by
    simpa [prefixWord, tailWord_674517, baseEnd_674517] using wordTrace_append hprefix tailTrace_674517
  have hstable : (prefixWord ++ tailWord_674517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674517).length < 2 ^ (prefixWord ++ tailWord_674517).sum := by decide
  have hdescent : baseEnd_674517 < baseStart_674517 := by decide
  rcases family_descends (prefixWord ++ tailWord_674517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674520 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_674520 : Nat := 118140960795 + 674520 * 2 ^ 59
def prefixEnd_674520 : Nat := 4983230072969 + 3 ^ 40 * 674520 * 2
def baseEnd_674520 : Nat := 346352971070806171097945

theorem tailTrace_674520 : CollatzResearch.WordTrace tailWord_674520 prefixEnd_674520 346352971070806171097945 := by
  unfold tailWord_674520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300882758168356844830507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16401177010891142459774009 12300882758168356844830507)
  ·
    refine ⟨18451324137252535267245761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12300882758168356844830507 18451324137252535267245761)
    ·
      refine ⟨13838493102939401450434321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18451324137252535267245761 13838493102939401450434321)
      ·
        refine ⟨10378869827204551087825741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13838493102939401450434321 10378869827204551087825741)
        ·
          refine ⟨3892076185201706657934653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10378869827204551087825741 3892076185201706657934653)
          ·
            refine ⟨1459528569450639996725495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3892076185201706657934653 1459528569450639996725495)
            ·
              refine ⟨2189292854175959995088243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459528569450639996725495 2189292854175959995088243)
              ·
                refine ⟨3283939281263939992632365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189292854175959995088243 3283939281263939992632365)
                ·
                  refine ⟨1231477230473977497237137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3283939281263939992632365 1231477230473977497237137)
                  ·
                    refine ⟨923607922855483122927853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1231477230473977497237137 923607922855483122927853)
                    ·
                      refine ⟨346352971070806171097945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923607922855483122927853 346352971070806171097945)
                      ·
                        rfl

theorem cell23_674520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_674520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674520 prefixEnd_674520 := by exact prefixLift 674520
  have htrace : WordTrace (prefixWord ++ tailWord_674520) baseStart_674520 baseEnd_674520 := by
    simpa [prefixWord, tailWord_674520, baseEnd_674520] using wordTrace_append hprefix tailTrace_674520
  have hstable : (prefixWord ++ tailWord_674520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674520).length < 2 ^ (prefixWord ++ tailWord_674520).sum := by decide
  have hdescent : baseEnd_674520 < baseStart_674520 := by decide
  rcases family_descends (prefixWord ++ tailWord_674520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674550 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_674550 : Nat := 118140960795 + 674550 * 2 ^ 59
def prefixEnd_674550 : Nat := 4983230072969 + 3 ^ 40 * 674550 * 2
def baseEnd_674550 : Nat := 346368375490441053722807

theorem tailTrace_674550 : CollatzResearch.WordTrace tailWord_674550 prefixEnd_674550 346368375490441053722807 := by
  unfold tailWord_674550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537678731639251800828319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16401906470818685875502069 1537678731639251800828319)
  ·
    refine ⟨2306518097458877701242479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537678731639251800828319 2306518097458877701242479)
    ·
      refine ⟨3459777146188316551863719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306518097458877701242479 3459777146188316551863719)
      ·
        refine ⟨5189665719282474827795579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3459777146188316551863719 5189665719282474827795579)
        ·
          refine ⟨7784498578923712241693369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189665719282474827795579 7784498578923712241693369)
          ·
            refine ⟨5838373934192784181270027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784498578923712241693369 5838373934192784181270027)
            ·
              refine ⟨8757560901289176271905041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838373934192784181270027 8757560901289176271905041)
              ·
                refine ⟨6568170675966882203928781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8757560901289176271905041 6568170675966882203928781)
                ·
                  refine ⟨2463064003487580826473293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6568170675966882203928781 2463064003487580826473293)
                  ·
                    refine ⟨923649001307842809927485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463064003487580826473293 923649001307842809927485)
                    ·
                      refine ⟨346368375490441053722807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923649001307842809927485 346368375490441053722807)
                      ·
                        rfl

theorem cell23_674550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_674550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674550 prefixEnd_674550 := by exact prefixLift 674550
  have htrace : WordTrace (prefixWord ++ tailWord_674550) baseStart_674550 baseEnd_674550 := by
    simpa [prefixWord, tailWord_674550, baseEnd_674550] using wordTrace_append hprefix tailTrace_674550
  have hstable : (prefixWord ++ tailWord_674550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674550).length < 2 ^ (prefixWord ++ tailWord_674550).sum := by decide
  have hdescent : baseEnd_674550 < baseStart_674550 := by decide
  rcases family_descends (prefixWord ++ tailWord_674550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674567 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_674567 : Nat := 118140960795 + 674567 * 2 ^ 59
def prefixEnd_674567 : Nat := 4983230072969 + 3 ^ 40 * 674567 * 2
def baseEnd_674567 : Nat := 346377104661567487210229

theorem tailTrace_674567 : CollatzResearch.WordTrace tailWord_674567 prefixEnd_674567 346377104661567487210229 := by
  unfold tailWord_674567
  simp only [CollatzResearch.WordTrace]
  refine ⟨24603479747166440716621955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16402319831444293811081303 24603479747166440716621955)
  ·
    refine ⟨36905219620749661074932933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24603479747166440716621955 36905219620749661074932933)
    ·
      refine ⟨6919728678890561451549925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36905219620749661074932933 6919728678890561451549925)
      ·
        refine ⟨1297449127291980272165611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6919728678890561451549925 1297449127291980272165611)
        ·
          refine ⟨1946173690937970408248417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297449127291980272165611 1946173690937970408248417)
          ·
            refine ⟨1459630268203477806186313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946173690937970408248417 1459630268203477806186313)
            ·
              refine ⟨1094722701152608354639735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459630268203477806186313 1094722701152608354639735)
              ·
                refine ⟨1642084051728912531959603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094722701152608354639735 1642084051728912531959603)
                ·
                  refine ⟨2463126077593368797939405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642084051728912531959603 2463126077593368797939405)
                  ·
                    refine ⟨923672279097513299227277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2463126077593368797939405 923672279097513299227277)
                    ·
                      refine ⟨346377104661567487210229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923672279097513299227277 346377104661567487210229)
                      ·
                        rfl

theorem cell23_674567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_674567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674567 prefixEnd_674567 := by exact prefixLift 674567
  have htrace : WordTrace (prefixWord ++ tailWord_674567) baseStart_674567 baseEnd_674567 := by
    simpa [prefixWord, tailWord_674567, baseEnd_674567] using wordTrace_append hprefix tailTrace_674567
  have hstable : (prefixWord ++ tailWord_674567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674567).length < 2 ^ (prefixWord ++ tailWord_674567).sum := by decide
  have hdescent : baseEnd_674567 < baseStart_674567 := by decide
  rcases family_descends (prefixWord ++ tailWord_674567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674593 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_674593 : Nat := 118140960795 + 674593 * 2 ^ 59
def prefixEnd_674593 : Nat := 4983230072969 + 3 ^ 40 * 674593 * 2
def baseEnd_674593 : Nat := 346390455158584385485109

theorem tailTrace_674593 : CollatzResearch.WordTrace tailWord_674593 prefixEnd_674593 346390455158584385485109 := by
  unfold tailWord_674593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24604428045072247157068433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16402952030048164771378955 24604428045072247157068433)
  ·
    refine ⟨18453321033804185367801325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24604428045072247157068433 18453321033804185367801325)
    ·
      refine ⟨6919995387676569512925497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18453321033804185367801325 6919995387676569512925497)
      ·
        refine ⟨5189996540757427134694123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6919995387676569512925497 5189996540757427134694123)
        ·
          refine ⟨7784994811136140702041185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5189996540757427134694123 7784994811136140702041185)
          ·
            refine ⟨5838746108352105526530889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7784994811136140702041185 5838746108352105526530889)
            ·
              refine ⟨4379059581264079144898167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5838746108352105526530889 4379059581264079144898167)
              ·
                refine ⟨6568589371896118717347251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379059581264079144898167 6568589371896118717347251)
                ·
                  refine ⟨9852884057844178076020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6568589371896118717347251 9852884057844178076020877)
                  ·
                    refine ⟨3694831521691566778507829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9852884057844178076020877 3694831521691566778507829)
                    ·
                      refine ⟨346390455158584385485109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3694831521691566778507829 346390455158584385485109)
                      ·
                        rfl

theorem cell23_674593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_674593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674593 prefixEnd_674593 := by exact prefixLift 674593
  have htrace : WordTrace (prefixWord ++ tailWord_674593) baseStart_674593 baseEnd_674593 := by
    simpa [prefixWord, tailWord_674593, baseEnd_674593] using wordTrace_append hprefix tailTrace_674593
  have hstable : (prefixWord ++ tailWord_674593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674593).length < 2 ^ (prefixWord ++ tailWord_674593).sum := by decide
  have hdescent : baseEnd_674593 < baseStart_674593 := by decide
  rcases family_descends (prefixWord ++ tailWord_674593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674594 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_674594 : Nat := 118140960795 + 674594 * 2 ^ 59
def prefixEnd_674594 : Nat := 4983230072969 + 3 ^ 40 * 674594 * 2
def baseEnd_674594 : Nat := 346390968639238881572605

theorem tailTrace_674594 : CollatzResearch.WordTrace tailWord_674594 prefixEnd_674594 346390968639238881572605 := by
  unfold tailWord_674594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6151116129517156081963709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16402976345379082885236557 6151116129517156081963709)
  ·
    refine ⟨2306668548568933530736391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6151116129517156081963709 2306668548568933530736391)
    ·
      refine ⟨3460002822853400296104587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306668548568933530736391 3460002822853400296104587)
      ·
        refine ⟨5190004234280100444156881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460002822853400296104587 5190004234280100444156881)
        ·
          refine ⟨3892503175710075333117661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190004234280100444156881 3892503175710075333117661)
          ·
            refine ⟨1459688690891278249919123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3892503175710075333117661 1459688690891278249919123)
            ·
              refine ⟨2189533036336917374878685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459688690891278249919123 2189533036336917374878685)
              ·
                refine ⟨821074888626344015579507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189533036336917374878685 821074888626344015579507)
                ·
                  refine ⟨1231612332939516023369261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821074888626344015579507 1231612332939516023369261)
                  ·
                    refine ⟨461854624852318508763473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231612332939516023369261 461854624852318508763473)
                    ·
                      refine ⟨346390968639238881572605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461854624852318508763473 346390968639238881572605)
                      ·
                        rfl

theorem cell23_674594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_674594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674594 prefixEnd_674594 := by exact prefixLift 674594
  have htrace : WordTrace (prefixWord ++ tailWord_674594) baseStart_674594 baseEnd_674594 := by
    simpa [prefixWord, tailWord_674594, baseEnd_674594] using wordTrace_append hprefix tailTrace_674594
  have hstable : (prefixWord ++ tailWord_674594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674594).length < 2 ^ (prefixWord ++ tailWord_674594).sum := by decide
  have hdescent : baseEnd_674594 < baseStart_674594 := by decide
  rcases family_descends (prefixWord ++ tailWord_674594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674603 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_674603 : Nat := 118140960795 + 674603 * 2 ^ 59
def prefixEnd_674603 : Nat := 4983230072969 + 3 ^ 40 * 674603 * 2
def baseEnd_674603 : Nat := 346395589965129346360063

theorem tailTrace_674603 : CollatzResearch.WordTrace tailWord_674603 prefixEnd_674603 346395589965129346360063 := by
  unfold tailWord_674603
  simp only [CollatzResearch.WordTrace]
  refine ⟨24604792775036018864932463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16403195183357345909954975 24604792775036018864932463)
  ·
    refine ⟨36907189162554028297398695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24604792775036018864932463 36907189162554028297398695)
    ·
      refine ⟨55360783743831042446098043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36907189162554028297398695 55360783743831042446098043)
      ·
        refine ⟨83041175615746563669147065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55360783743831042446098043 83041175615746563669147065)
        ·
          refine ⟨62280881711809922751860299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83041175615746563669147065 62280881711809922751860299)
          ·
            refine ⟨93421322567714884127790449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62280881711809922751860299 93421322567714884127790449)
            ·
              refine ⟨70065991925786163095842837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93421322567714884127790449 70065991925786163095842837)
              ·
                refine ⟨3284343371521226395117633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70065991925786163095842837 3284343371521226395117633)
                ·
                  refine ⟨2463257528640919796338225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284343371521226395117633 2463257528640919796338225)
                  ·
                    refine ⟨1847443146480689847253669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2463257528640919796338225 1847443146480689847253669)
                    ·
                      refine ⟨346395589965129346360063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1847443146480689847253669 346395589965129346360063)
                      ·
                        rfl

theorem cell23_674603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_674603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674603 prefixEnd_674603 := by exact prefixLift 674603
  have htrace : WordTrace (prefixWord ++ tailWord_674603) baseStart_674603 baseEnd_674603 := by
    simpa [prefixWord, tailWord_674603, baseEnd_674603] using wordTrace_append hprefix tailTrace_674603
  have hstable : (prefixWord ++ tailWord_674603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674603).length < 2 ^ (prefixWord ++ tailWord_674603).sum := by decide
  have hdescent : baseEnd_674603 < baseStart_674603 := by decide
  rcases family_descends (prefixWord ++ tailWord_674603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674628 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_674628 : Nat := 118140960795 + 674628 * 2 ^ 59
def prefixEnd_674628 : Nat := 4983230072969 + 3 ^ 40 * 674628 * 2
def baseEnd_674628 : Nat := 346408426981491748547449

theorem tailTrace_674628 : CollatzResearch.WordTrace tailWord_674628 prefixEnd_674628 346408426981491748547449 := by
  unfold tailWord_674628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12302852299972724067296269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16403803066630298756395025 12302852299972724067296269)
  ·
    refine ⟨4613569612489771525236101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12302852299972724067296269 4613569612489771525236101)
    ·
      refine ⟨865044302341832160981769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4613569612489771525236101 865044302341832160981769)
      ·
        refine ⟨648783226756374120736327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 865044302341832160981769 648783226756374120736327)
        ·
          refine ⟨973174840134561181104491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648783226756374120736327 973174840134561181104491)
          ·
            refine ⟨1459762260201841771656737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973174840134561181104491 1459762260201841771656737)
            ·
              refine ⟨1094821695151381328742553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459762260201841771656737 1094821695151381328742553)
              ·
                refine ⟨821116271363535996556915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094821695151381328742553 821116271363535996556915)
                ·
                  refine ⟨1231674407045303994835373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821116271363535996556915 1231674407045303994835373)
                  ·
                    refine ⟨461877902641988998063265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1231674407045303994835373 461877902641988998063265)
                    ·
                      refine ⟨346408426981491748547449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 461877902641988998063265 346408426981491748547449)
                      ·
                        rfl

theorem cell23_674628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_674628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674628 prefixEnd_674628 := by exact prefixLift 674628
  have htrace : WordTrace (prefixWord ++ tailWord_674628) baseStart_674628 baseEnd_674628 := by
    simpa [prefixWord, tailWord_674628, baseEnd_674628] using wordTrace_append hprefix tailTrace_674628
  have hstable : (prefixWord ++ tailWord_674628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674628).length < 2 ^ (prefixWord ++ tailWord_674628).sum := by decide
  have hdescent : baseEnd_674628 < baseStart_674628 := by decide
  rcases family_descends (prefixWord ++ tailWord_674628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674643 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 6, 5]
def baseStart_674643 : Nat := 118140960795 + 674643 * 2 ^ 59
def prefixEnd_674643 : Nat := 4983230072969 + 3 ^ 40 * 674643 * 2
def baseEnd_674643 : Nat := 115472043063769729953293

theorem tailTrace_674643 : CollatzResearch.WordTrace tailWord_674643 prefixEnd_674643 115472043063769729953293 := by
  unfold tailWord_674643
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606251694891105696388583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16404167796594070464259055 24606251694891105696388583)
  ·
    refine ⟨36909377542336658544582875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24606251694891105696388583 36909377542336658544582875)
    ·
      refine ⟨55364066313504987816874313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36909377542336658544582875 55364066313504987816874313)
      ·
        refine ⟨41523049735128740862655735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55364066313504987816874313 41523049735128740862655735)
        ·
          refine ⟨62284574602693111293983603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41523049735128740862655735 62284574602693111293983603)
          ·
            refine ⟨93426861904039666940975405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62284574602693111293983603 93426861904039666940975405)
            ·
              refine ⟨35035073214014875102865777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93426861904039666940975405 35035073214014875102865777)
              ·
                refine ⟨26276304910511156327149333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35035073214014875102865777 26276304910511156327149333)
                ·
                  refine ⟨1231701792680210452835125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26276304910511156327149333 1231701792680210452835125)
                  ·
                    refine ⟨115472043063769729953293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1231701792680210452835125 115472043063769729953293)
                    ·
                      rfl

theorem cell23_674643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 5].length) (baseStart_674643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674643 prefixEnd_674643 := by exact prefixLift 674643
  have htrace : WordTrace (prefixWord ++ tailWord_674643) baseStart_674643 baseEnd_674643 := by
    simpa [prefixWord, tailWord_674643, baseEnd_674643] using wordTrace_append hprefix tailTrace_674643
  have hstable : (prefixWord ++ tailWord_674643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674643).length < 2 ^ (prefixWord ++ tailWord_674643).sum := by decide
  have hdescent : baseEnd_674643 < baseStart_674643 := by decide
  rcases family_descends (prefixWord ++ tailWord_674643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674647 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 5]
def baseStart_674647 : Nat := 118140960795 + 674647 * 2 ^ 59
def prefixEnd_674647 : Nat := 4983230072969 + 3 ^ 40 * 674647 * 2
def baseEnd_674647 : Nat := 38490909234880797134429

theorem tailTrace_674647 : CollatzResearch.WordTrace tailWord_674647 prefixEnd_674647 38490909234880797134429 := by
  unfold tailWord_674647
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606397586876614379534195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16404265057917742919689463 24606397586876614379534195)
  ·
    refine ⟨36909596380314921569301293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24606397586876614379534195 36909596380314921569301293)
    ·
      refine ⟨13841098642618095588487985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36909596380314921569301293 13841098642618095588487985)
      ·
        refine ⟨10380823981963571691365989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13841098642618095588487985 10380823981963571691365989)
        ·
          refine ⟨1946404496618169692131123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10380823981963571691365989 1946404496618169692131123)
          ·
            refine ⟨2919606744927254538196685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946404496618169692131123 2919606744927254538196685)
            ·
              refine ⟨1094852529347720451823757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2919606744927254538196685 1094852529347720451823757)
              ·
                refine ⟨410569698505395169433909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1094852529347720451823757 410569698505395169433909)
                ·
                  refine ⟨38490909234880797134429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410569698505395169433909 38490909234880797134429)
                  ·
                    rfl

theorem cell23_674647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 5].length) (baseStart_674647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674647 prefixEnd_674647 := by exact prefixLift 674647
  have htrace : WordTrace (prefixWord ++ tailWord_674647) baseStart_674647 baseEnd_674647 := by
    simpa [prefixWord, tailWord_674647, baseEnd_674647] using wordTrace_append hprefix tailTrace_674647
  have hstable : (prefixWord ++ tailWord_674647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674647).length < 2 ^ (prefixWord ++ tailWord_674647).sum := by decide
  have hdescent : baseEnd_674647 < baseStart_674647 := by decide
  rcases family_descends (prefixWord ++ tailWord_674647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674660 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_674660 : Nat := 118140960795 + 674660 * 2 ^ 59
def prefixEnd_674660 : Nat := 4983230072969 + 3 ^ 40 * 674660 * 2
def baseEnd_674660 : Nat := 115474952787478541115767

theorem tailTrace_674660 : CollatzResearch.WordTrace tailWord_674660 prefixEnd_674660 115474952787478541115767 := by
  unfold tailWord_674660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303435867914758799878717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16404581157219678399838289 12303435867914758799878717)
  ·
    refine ⟨4613788450468034549954519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12303435867914758799878717 4613788450468034549954519)
    ·
      refine ⟨6920682675702051824931779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613788450468034549954519 6920682675702051824931779)
      ·
        refine ⟨10381024013553077737397669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920682675702051824931779 10381024013553077737397669)
        ·
          refine ⟨1946442002541202075762063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10381024013553077737397669 1946442002541202075762063)
          ·
            refine ⟨2919663003811803113643095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946442002541202075762063 2919663003811803113643095)
            ·
              refine ⟨4379494505717704670464643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919663003811803113643095 4379494505717704670464643)
              ·
                refine ⟨6569241758576557005696965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379494505717704670464643 6569241758576557005696965)
                ·
                  refine ⟨1231732829733104438568181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6569241758576557005696965 1231732829733104438568181)
                  ·
                    refine ⟨115474952787478541115767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1231732829733104438568181 115474952787478541115767)
                    ·
                      rfl

theorem cell23_674660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_674660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674660 prefixEnd_674660 := by exact prefixLift 674660
  have htrace : WordTrace (prefixWord ++ tailWord_674660) baseStart_674660 baseEnd_674660 := by
    simpa [prefixWord, tailWord_674660, baseEnd_674660] using wordTrace_append hprefix tailTrace_674660
  have hstable : (prefixWord ++ tailWord_674660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674660).length < 2 ^ (prefixWord ++ tailWord_674660).sum := by decide
  have hdescent : baseEnd_674660 < baseStart_674660 := by decide
  rcases family_descends (prefixWord ++ tailWord_674660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674664 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 5]
def baseStart_674664 : Nat := 118140960795 + 674664 * 2 ^ 59
def prefixEnd_674664 : Nat := 4983230072969 + 3 ^ 40 * 674664 * 2
def baseEnd_674664 : Nat := 38491879142783734188587

theorem tailTrace_674664 : CollatzResearch.WordTrace tailWord_674664 prefixEnd_674664 38491879142783734188587 := by
  unfold tailWord_674664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303508813907513141451523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16404678418543350855268697 12303508813907513141451523)
  ·
    refine ⟨18455263220861269712177285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12303508813907513141451523 18455263220861269712177285)
    ·
      refine ⟨3460361853911488071033241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18455263220861269712177285 3460361853911488071033241)
      ·
        refine ⟨2595271390433616053274931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460361853911488071033241 2595271390433616053274931)
        ·
          refine ⟨3892907085650424079912397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595271390433616053274931 3892907085650424079912397)
          ·
            refine ⟨1459840157118909029967149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3892907085650424079912397 1459840157118909029967149)
            ·
              refine ⟨547440058919590886237681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1459840157118909029967149 547440058919590886237681)
              ·
                refine ⟨410580044189693164678261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547440058919590886237681 410580044189693164678261)
                ·
                  refine ⟨38491879142783734188587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410580044189693164678261 38491879142783734188587)
                  ·
                    rfl

theorem cell23_674664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 5].length) (baseStart_674664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674664 prefixEnd_674664 := by exact prefixLift 674664
  have htrace : WordTrace (prefixWord ++ tailWord_674664) baseStart_674664 baseEnd_674664 := by
    simpa [prefixWord, tailWord_674664, baseEnd_674664] using wordTrace_append hprefix tailTrace_674664
  have hstable : (prefixWord ++ tailWord_674664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674664).length < 2 ^ (prefixWord ++ tailWord_674664).sum := by decide
  have hdescent : baseEnd_674664 < baseStart_674664 := by decide
  rcases family_descends (prefixWord ++ tailWord_674664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674697 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_674697 : Nat := 118140960795 + 674697 * 2 ^ 59
def prefixEnd_674697 : Nat := 4983230072969 + 3 ^ 40 * 674697 * 2
def baseEnd_674697 : Nat := 346443857146651978584631

theorem tailTrace_674697 : CollatzResearch.WordTrace tailWord_674697 prefixEnd_674697 346443857146651978584631 := by
  unfold tailWord_674697
  simp only [CollatzResearch.WordTrace]
  refine ⟨24608221236695472918854345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16405480824463648612569563 24608221236695472918854345)
  ·
    refine ⟨18456165927521604689140759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24608221236695472918854345 18456165927521604689140759)
    ·
      refine ⟨27684248891282407033711139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18456165927521604689140759 27684248891282407033711139)
      ·
        refine ⟨41526373336923610550566709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27684248891282407033711139 41526373336923610550566709)
        ·
          refine ⟨3893097500336588489115629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41526373336923610550566709 3893097500336588489115629)
          ·
            refine ⟨1459911562626220683418361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3893097500336588489115629 1459911562626220683418361)
            ·
              refine ⟨1094933671969665512563771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459911562626220683418361 1094933671969665512563771)
              ·
                refine ⟨1642400507954498268845657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094933671969665512563771 1642400507954498268845657)
                ·
                  refine ⟨1231800380965873701634243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642400507954498268845657 1231800380965873701634243)
                  ·
                    refine ⟨1847700571448810552451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231800380965873701634243 1847700571448810552451365)
                    ·
                      refine ⟨346443857146651978584631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1847700571448810552451365 346443857146651978584631)
                      ·
                        rfl

theorem cell23_674697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_674697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674697 prefixEnd_674697 := by exact prefixLift 674697
  have htrace : WordTrace (prefixWord ++ tailWord_674697) baseStart_674697 baseEnd_674697 := by
    simpa [prefixWord, tailWord_674697, baseEnd_674697] using wordTrace_append hprefix tailTrace_674697
  have hstable : (prefixWord ++ tailWord_674697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674697).length < 2 ^ (prefixWord ++ tailWord_674697).sum := by decide
  have hdescent : baseEnd_674697 < baseStart_674697 := by decide
  rcases family_descends (prefixWord ++ tailWord_674697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674700 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_674700 : Nat := 118140960795 + 674700 * 2 ^ 59
def prefixEnd_674700 : Nat := 4983230072969 + 3 ^ 40 * 674700 * 2
def baseEnd_674700 : Nat := 346445397588615466847117

theorem tailTrace_674700 : CollatzResearch.WordTrace tailWord_674700 prefixEnd_674700 346445397588615466847117 := by
  unfold tailWord_674700
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304165327842302215606777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16405553770456402954142369 12304165327842302215606777)
  ·
    refine ⟨9228123995881726661705083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12304165327842302215606777 9228123995881726661705083)
    ·
      refine ⟨13842185993822589992557625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9228123995881726661705083 13842185993822589992557625)
      ·
        refine ⟨10381639495366942494418219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13842185993822589992557625 10381639495366942494418219)
        ·
          refine ⟨15572459243050413741627329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381639495366942494418219 15572459243050413741627329)
          ·
            refine ⟨11679344432287810306220497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15572459243050413741627329 11679344432287810306220497)
            ·
              refine ⟨8759508324215857729665373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11679344432287810306220497 8759508324215857729665373)
              ·
                refine ⟨3284815621580946648624515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8759508324215857729665373 3284815621580946648624515)
                ·
                  refine ⟨4927223432371419972936773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3284815621580946648624515 4927223432371419972936773)
                  ·
                    refine ⟨923854393569641244925645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4927223432371419972936773 923854393569641244925645)
                    ·
                      refine ⟨346445397588615466847117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923854393569641244925645 346445397588615466847117)
                      ·
                        rfl

theorem cell23_674700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_674700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674700 prefixEnd_674700 := by exact prefixLift 674700
  have htrace : WordTrace (prefixWord ++ tailWord_674700) baseStart_674700 baseEnd_674700 := by
    simpa [prefixWord, tailWord_674700, baseEnd_674700] using wordTrace_append hprefix tailTrace_674700
  have hstable : (prefixWord ++ tailWord_674700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674700).length < 2 ^ (prefixWord ++ tailWord_674700).sum := by decide
  have hdescent : baseEnd_674700 < baseStart_674700 := by decide
  rcases family_descends (prefixWord ++ tailWord_674700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674717 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_674717 : Nat := 118140960795 + 674717 * 2 ^ 59
def prefixEnd_674717 : Nat := 4983230072969 + 3 ^ 40 * 674717 * 2
def baseEnd_674717 : Nat := 346454126759741900334539

theorem tailTrace_674717 : CollatzResearch.WordTrace tailWord_674717 prefixEnd_674717 346454126759741900334539 := by
  unfold tailWord_674717
  simp only [CollatzResearch.WordTrace]
  refine ⟨24608950696623016334582405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16405967131082010889721603 24608950696623016334582405)
  ·
    refine ⟨4614178255616815562734201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24608950696623016334582405 4614178255616815562734201)
    ·
      refine ⟨3460633691712611672050651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614178255616815562734201 3460633691712611672050651)
      ·
        refine ⟨5190950537568917508075977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460633691712611672050651 5190950537568917508075977)
        ·
          refine ⟨3893212903176688131056983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5190950537568917508075977 3893212903176688131056983)
          ·
            refine ⟨5839819354765032196585475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893212903176688131056983 5839819354765032196585475)
            ·
              refine ⟨8759729032147548294878213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839819354765032196585475 8759729032147548294878213)
              ·
                refine ⟨1642449193527665305289665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8759729032147548294878213 1642449193527665305289665)
                ·
                  refine ⟨1231836895145748978967249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642449193527665305289665 1231836895145748978967249)
                  ·
                    refine ⟨923877671359311734225437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1231836895145748978967249 923877671359311734225437)
                    ·
                      refine ⟨346454126759741900334539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923877671359311734225437 346454126759741900334539)
                      ·
                        rfl

theorem cell23_674717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_674717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674717 prefixEnd_674717 := by exact prefixLift 674717
  have htrace : WordTrace (prefixWord ++ tailWord_674717) baseStart_674717 baseEnd_674717 := by
    simpa [prefixWord, tailWord_674717, baseEnd_674717] using wordTrace_append hprefix tailTrace_674717
  have hstable : (prefixWord ++ tailWord_674717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674717).length < 2 ^ (prefixWord ++ tailWord_674717).sum := by decide
  have hdescent : baseEnd_674717 < baseStart_674717 := by decide
  rcases family_descends (prefixWord ++ tailWord_674717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674720 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 6]
def baseStart_674720 : Nat := 118140960795 + 674720 * 2 ^ 59
def prefixEnd_674720 : Nat := 4983230072969 + 3 ^ 40 * 674720 * 2
def baseEnd_674720 : Nat := 38495074133522820955225

theorem tailTrace_674720 : CollatzResearch.WordTrace tailWord_674720 prefixEnd_674720 38495074133522820955225 := by
  unfold tailWord_674720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304530057806073923470807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16406040077074765231294409 12304530057806073923470807)
  ·
    refine ⟨18456795086709110885206211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12304530057806073923470807 18456795086709110885206211)
    ·
      refine ⟨27685192630063666327809317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18456795086709110885206211 27685192630063666327809317)
      ·
        refine ⟨5190973618136937436464247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27685192630063666327809317 5190973618136937436464247)
        ·
          refine ⟨7786460427205406154696371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190973618136937436464247 7786460427205406154696371)
          ·
            refine ⟨11679690640808109232044557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786460427205406154696371 11679690640808109232044557)
            ·
              refine ⟨4379883990303040962016709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11679690640808109232044557 4379883990303040962016709)
              ·
                refine ⟨821228248181820180378133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4379883990303040962016709 821228248181820180378133)
                ·
                  refine ⟨38495074133522820955225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 821228248181820180378133 38495074133522820955225)
                  ·
                    rfl

theorem cell23_674720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_674720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674720 prefixEnd_674720 := by exact prefixLift 674720
  have htrace : WordTrace (prefixWord ++ tailWord_674720) baseStart_674720 baseEnd_674720 := by
    simpa [prefixWord, tailWord_674720, baseEnd_674720] using wordTrace_append hprefix tailTrace_674720
  have hstable : (prefixWord ++ tailWord_674720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674720).length < 2 ^ (prefixWord ++ tailWord_674720).sum := by decide
  have hdescent : baseEnd_674720 < baseStart_674720 := by decide
  rcases family_descends (prefixWord ++ tailWord_674720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674724 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_674724 : Nat := 118140960795 + 674724 * 2 ^ 59
def prefixEnd_674724 : Nat := 4983230072969 + 3 ^ 40 * 674724 * 2
def baseEnd_674724 : Nat := 115485907041441124315669

theorem tailTrace_674724 : CollatzResearch.WordTrace tailWord_674724 prefixEnd_674724 115485907041441124315669 := by
  unfold tailWord_674724
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304603003798828265043613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16406137338398437686724817 12304603003798828265043613)
  ·
    refine ⟨4614226126424560599391355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12304603003798828265043613 4614226126424560599391355)
    ·
      refine ⟨6921339189636840899087033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614226126424560599391355 6921339189636840899087033)
      ·
        refine ⟨5191004392227630674315275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921339189636840899087033 5191004392227630674315275)
        ·
          refine ⟨7786506588341446011472913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191004392227630674315275 7786506588341446011472913)
          ·
            refine ⟨5839879941256084508604685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7786506588341446011472913 5839879941256084508604685)
            ·
              refine ⟨2189954977971031690726757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5839879941256084508604685 2189954977971031690726757)
              ·
                refine ⟨410616558369568442011267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2189954977971031690726757 410616558369568442011267)
                ·
                  refine ⟨615924837554352663016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410616558369568442011267 615924837554352663016901)
                  ·
                    refine ⟨115485907041441124315669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615924837554352663016901 115485907041441124315669)
                    ·
                      rfl

theorem cell23_674724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_674724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674724 prefixEnd_674724 := by exact prefixLift 674724
  have htrace : WordTrace (prefixWord ++ tailWord_674724) baseStart_674724 baseEnd_674724 := by
    simpa [prefixWord, tailWord_674724, baseEnd_674724] using wordTrace_append hprefix tailTrace_674724
  have hstable : (prefixWord ++ tailWord_674724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674724).length < 2 ^ (prefixWord ++ tailWord_674724).sum := by decide
  have hdescent : baseEnd_674724 < baseStart_674724 := by decide
  rcases family_descends (prefixWord ++ tailWord_674724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674767 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 1, 5]
def baseStart_674767 : Nat := 118140960795 + 674767 * 2 ^ 59
def prefixEnd_674767 : Nat := 4983230072969 + 3 ^ 40 * 674767 * 2
def baseEnd_674767 : Nat := 115493266930822234903103

theorem tailTrace_674767 : CollatzResearch.WordTrace tailWord_674767 prefixEnd_674767 115493266930822234903103 := by
  unfold tailWord_674767
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610774346441874873902555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16407182897627916582601703 24610774346441874873902555)
  ·
    refine ⟨36916161519662812310853833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24610774346441874873902555 36916161519662812310853833)
    ·
      refine ⟨27687121139747109233140375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36916161519662812310853833 27687121139747109233140375)
      ·
        refine ⟨41530681709620663849710563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27687121139747109233140375 41530681709620663849710563)
        ·
          refine ⟨62296022564430995774565845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41530681709620663849710563 62296022564430995774565845)
          ·
            refine ⟨1460063028853851463466387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62296022564430995774565845 1460063028853851463466387)
            ·
              refine ⟨2190094543280777195199581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460063028853851463466387 2190094543280777195199581)
              ·
                refine ⟨821285453730291448199843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190094543280777195199581 821285453730291448199843)
                ·
                  refine ⟨1231928180595437172299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821285453730291448199843 1231928180595437172299765)
                  ·
                    refine ⟨115493266930822234903103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1231928180595437172299765 115493266930822234903103)
                    ·
                      rfl

theorem cell23_674767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_674767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674767 prefixEnd_674767 := by exact prefixLift 674767
  have htrace : WordTrace (prefixWord ++ tailWord_674767) baseStart_674767 baseEnd_674767 := by
    simpa [prefixWord, tailWord_674767, baseEnd_674767] using wordTrace_append hprefix tailTrace_674767
  have hstable : (prefixWord ++ tailWord_674767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674767).length < 2 ^ (prefixWord ++ tailWord_674767).sum := by decide
  have hdescent : baseEnd_674767 < baseStart_674767 := by decide
  rcases family_descends (prefixWord ++ tailWord_674767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674781 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_674781 : Nat := 118140960795 + 674781 * 2 ^ 59
def prefixEnd_674781 : Nat := 4983230072969 + 3 ^ 40 * 674781 * 2
def baseEnd_674781 : Nat := 346486989521629649934245

theorem tailTrace_674781 : CollatzResearch.WordTrace tailWord_674781 prefixEnd_674781 346486989521629649934245 := by
  unfold tailWord_674781
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611284968391155264912197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16407523312260770176608131 24611284968391155264912197)
  ·
    refine ⟨4614615931573341612171037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24611284968391155264912197 4614615931573341612171037)
    ·
      refine ⟨1730480974340003104564139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4614615931573341612171037 1730480974340003104564139)
      ·
        refine ⟨2595721461510004656846209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730480974340003104564139 2595721461510004656846209)
        ·
          refine ⟨1946791096132503492634657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595721461510004656846209 1946791096132503492634657)
          ·
            refine ⟨1460093322099377619475993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946791096132503492634657 1460093322099377619475993)
            ·
              refine ⟨1095069991574533214606995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460093322099377619475993 1095069991574533214606995)
              ·
                refine ⟨1642604987361799821910493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095069991574533214606995 1642604987361799821910493)
                ·
                  refine ⟨615976870260674933216435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1642604987361799821910493 615976870260674933216435)
                  ·
                    refine ⟨923965305391012399824653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 615976870260674933216435 923965305391012399824653)
                    ·
                      refine ⟨346486989521629649934245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 923965305391012399824653 346486989521629649934245)
                      ·
                        rfl

theorem cell23_674781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_674781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674781 prefixEnd_674781 := by exact prefixLift 674781
  have htrace : WordTrace (prefixWord ++ tailWord_674781) baseStart_674781 baseEnd_674781 := by
    simpa [prefixWord, tailWord_674781, baseEnd_674781] using wordTrace_append hprefix tailTrace_674781
  have hstable : (prefixWord ++ tailWord_674781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674781).length < 2 ^ (prefixWord ++ tailWord_674781).sum := by decide
  have hdescent : baseEnd_674781 < baseStart_674781 := by decide
  rcases family_descends (prefixWord ++ tailWord_674781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674824 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_674824 : Nat := 118140960795 + 674824 * 2 ^ 59
def prefixEnd_674824 : Nat := 4983230072969 + 3 ^ 40 * 674824 * 2
def baseEnd_674824 : Nat := 346509069189772981696547

theorem tailTrace_674824 : CollatzResearch.WordTrace tailWord_674824 prefixEnd_674824 346509069189772981696547 := by
  unfold tailWord_674824
  simp only [CollatzResearch.WordTrace]
  refine ⟨12306426653617686804363763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16408568871490249072485017 12306426653617686804363763)
  ·
    refine ⟨18459639980426530206545645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12306426653617686804363763 18459639980426530206545645)
    ·
      refine ⟨6922364992659948827454617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18459639980426530206545645 6922364992659948827454617)
      ·
        refine ⟨5191773744494961620590963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6922364992659948827454617 5191773744494961620590963)
        ·
          refine ⟨7787660616742442430886445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191773744494961620590963 7787660616742442430886445)
          ·
            refine ⟨2920372731278415911582417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7787660616742442430886445 2920372731278415911582417)
            ·
              refine ⟨2190279548458811933686813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920372731278415911582417 2190279548458811933686813)
              ·
                refine ⟨821354830672054475132555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190279548458811933686813 821354830672054475132555)
                ·
                  refine ⟨1232032246008081712698833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821354830672054475132555 1232032246008081712698833)
                  ·
                    refine ⟨924024184506061284524125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232032246008081712698833 924024184506061284524125)
                    ·
                      refine ⟨346509069189772981696547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924024184506061284524125 346509069189772981696547)
                      ·
                        rfl

theorem cell23_674824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_674824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674824 prefixEnd_674824 := by exact prefixLift 674824
  have htrace : WordTrace (prefixWord ++ tailWord_674824) baseStart_674824 baseEnd_674824 := by
    simpa [prefixWord, tailWord_674824, baseEnd_674824] using wordTrace_append hprefix tailTrace_674824
  have hstable : (prefixWord ++ tailWord_674824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674824).length < 2 ^ (prefixWord ++ tailWord_674824).sum := by decide
  have hdescent : baseEnd_674824 < baseStart_674824 := by decide
  rcases family_descends (prefixWord ++ tailWord_674824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674858 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_674858 : Nat := 118140960795 + 674858 * 2 ^ 59
def prefixEnd_674858 : Nat := 4983230072969 + 3 ^ 40 * 674858 * 2
def baseEnd_674858 : Nat := 346526527532025848671391

theorem tailTrace_674858 : CollatzResearch.WordTrace tailWord_674858 prefixEnd_674858 346526527532025848671391 := by
  unfold tailWord_674858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153523347278049353866307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16409395592741464943643485 6153523347278049353866307)
  ·
    refine ⟨9230285020917074030799461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6153523347278049353866307 9230285020917074030799461)
    ·
      refine ⟨1730678441421951380774899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9230285020917074030799461 1730678441421951380774899)
      ·
        refine ⟨2596017662132927071162349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730678441421951380774899 2596017662132927071162349)
        ·
          refine ⟨973506623299847651685881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2596017662132927071162349 973506623299847651685881)
          ·
            refine ⟨730129967474885738764411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973506623299847651685881 730129967474885738764411)
            ·
              refine ⟨1095194951212328608146617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730129967474885738764411 1095194951212328608146617)
              ·
                refine ⟨821396213409246456109963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095194951212328608146617 821396213409246456109963)
                ·
                  refine ⟨1232094320113869684164945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821396213409246456109963 1232094320113869684164945)
                  ·
                    refine ⟨924070740085402263123709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232094320113869684164945 924070740085402263123709)
                    ·
                      refine ⟨346526527532025848671391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924070740085402263123709 346526527532025848671391)
                      ·
                        rfl

theorem cell23_674858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_674858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674858 prefixEnd_674858 := by exact prefixLift 674858
  have htrace : WordTrace (prefixWord ++ tailWord_674858) baseStart_674858 baseEnd_674858 := by
    simpa [prefixWord, tailWord_674858, baseEnd_674858] using wordTrace_append hprefix tailTrace_674858
  have hstable : (prefixWord ++ tailWord_674858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674858).length < 2 ^ (prefixWord ++ tailWord_674858).sum := by decide
  have hdescent : baseEnd_674858 < baseStart_674858 := by decide
  rcases family_descends (prefixWord ++ tailWord_674858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674864 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2]
def baseStart_674864 : Nat := 118140960795 + 674864 * 2 ^ 59
def prefixEnd_674864 : Nat := 4983230072969 + 3 ^ 40 * 674864 * 2
def baseEnd_674864 : Nat := 346529608415952825196363

theorem tailTrace_674864 : CollatzResearch.WordTrace tailWord_674864 prefixEnd_674864 346529608415952825196363 := by
  unfold tailWord_674864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307156113545230220091823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16409541484726973626789097 12307156113545230220091823)
  ·
    refine ⟨18460734170317845330137735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12307156113545230220091823 18460734170317845330137735)
    ·
      refine ⟨27691101255476767995206603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18460734170317845330137735 27691101255476767995206603)
      ·
        refine ⟨41536651883215151992809905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27691101255476767995206603 41536651883215151992809905)
        ·
          refine ⟨31152488912411363994607429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41536651883215151992809905 31152488912411363994607429)
          ·
            refine ⟨5841091671077130748988893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31152488912411363994607429 5841091671077130748988893)
            ·
              refine ⟨2190409376653924030870835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5841091671077130748988893 2190409376653924030870835)
              ·
                refine ⟨3285614064980886046306253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190409376653924030870835 3285614064980886046306253)
                ·
                  refine ⟨1232105274367832267364845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3285614064980886046306253 1232105274367832267364845)
                  ·
                    refine ⟨462039477887937100261817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232105274367832267364845 462039477887937100261817)
                    ·
                      refine ⟨346529608415952825196363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462039477887937100261817 346529608415952825196363)
                      ·
                        rfl

theorem cell23_674864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2].length) (baseStart_674864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674864 prefixEnd_674864 := by exact prefixLift 674864
  have htrace : WordTrace (prefixWord ++ tailWord_674864) baseStart_674864 baseEnd_674864 := by
    simpa [prefixWord, tailWord_674864, baseEnd_674864] using wordTrace_append hprefix tailTrace_674864
  have hstable : (prefixWord ++ tailWord_674864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674864).length < 2 ^ (prefixWord ++ tailWord_674864).sum := by decide
  have hdescent : baseEnd_674864 < baseStart_674864 := by decide
  rcases family_descends (prefixWord ++ tailWord_674864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674894 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_674894 : Nat := 118140960795 + 674894 * 2 ^ 59
def prefixEnd_674894 : Nat := 4983230072969 + 3 ^ 40 * 674894 * 2
def baseEnd_674894 : Nat := 346545012835587707821225

theorem tailTrace_674894 : CollatzResearch.WordTrace tailWord_674894 prefixEnd_674894 346545012835587707821225 := by
  unfold tailWord_674894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076925802122721945471967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16410270944654517042517157 3076925802122721945471967)
  ·
    refine ⟨4615388703184082918207951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076925802122721945471967 4615388703184082918207951)
    ·
      refine ⟨6923083054776124377311927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615388703184082918207951 6923083054776124377311927)
      ·
        refine ⟨10384624582164186565967891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923083054776124377311927 10384624582164186565967891)
        ·
          refine ⟨15576936873246279848951837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384624582164186565967891 15576936873246279848951837)
          ·
            refine ⟨5841351327467354943356939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15576936873246279848951837 5841351327467354943356939)
            ·
              refine ⟨8762026991201032415035409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841351327467354943356939 8762026991201032415035409)
              ·
                refine ⟨6571520243400774311276557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762026991201032415035409 6571520243400774311276557)
                ·
                  refine ⟨2464320091275290366728709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6571520243400774311276557 2464320091275290366728709)
                  ·
                    refine ⟨462060017114116943761633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2464320091275290366728709 462060017114116943761633)
                    ·
                      refine ⟨346545012835587707821225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462060017114116943761633 346545012835587707821225)
                      ·
                        rfl

theorem cell23_674894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_674894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674894 prefixEnd_674894 := by exact prefixLift 674894
  have htrace : WordTrace (prefixWord ++ tailWord_674894) baseStart_674894 baseEnd_674894 := by
    simpa [prefixWord, tailWord_674894, baseEnd_674894] using wordTrace_append hprefix tailTrace_674894
  have hstable : (prefixWord ++ tailWord_674894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674894).length < 2 ^ (prefixWord ++ tailWord_674894).sum := by decide
  have hdescent : baseEnd_674894 < baseStart_674894 := by decide
  rcases family_descends (prefixWord ++ tailWord_674894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674897 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_674897 : Nat := 118140960795 + 674897 * 2 ^ 59
def prefixEnd_674897 : Nat := 4983230072969 + 3 ^ 40 * 674897 * 2
def baseEnd_674897 : Nat := 346546553277551196083711

theorem tailTrace_674897 : CollatzResearch.WordTrace tailWord_674897 prefixEnd_674897 346546553277551196083711 := by
  unfold tailWord_674897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24615515835970907076134945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16410343890647271384089963 24615515835970907076134945)
  ·
    refine ⟨18461636876978180307101209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24615515835970907076134945 18461636876978180307101209)
    ·
      refine ⟨13846227657733635230325907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18461636876978180307101209 13846227657733635230325907)
      ·
        refine ⟨20769341486600452845488861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13846227657733635230325907 20769341486600452845488861)
        ·
          refine ⟨7788503057475169817058323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20769341486600452845488861 7788503057475169817058323)
          ·
            refine ⟨11682754586212754725587485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7788503057475169817058323 11682754586212754725587485)
            ·
              refine ⟨4381032969829783022095307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11682754586212754725587485 4381032969829783022095307)
              ·
                refine ⟨6571549454744674533142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381032969829783022095307 6571549454744674533142961)
                ·
                  refine ⟨4928662091058505899857221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6571549454744674533142961 4928662091058505899857221)
                  ·
                    refine ⟨924124142073469856223229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928662091058505899857221 924124142073469856223229)
                    ·
                      refine ⟨346546553277551196083711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924124142073469856223229 346546553277551196083711)
                      ·
                        rfl

theorem cell23_674897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_674897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674897 prefixEnd_674897 := by exact prefixLift 674897
  have htrace : WordTrace (prefixWord ++ tailWord_674897) baseStart_674897 baseEnd_674897 := by
    simpa [prefixWord, tailWord_674897, baseEnd_674897] using wordTrace_append hprefix tailTrace_674897
  have hstable : (prefixWord ++ tailWord_674897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674897).length < 2 ^ (prefixWord ++ tailWord_674897).sum := by decide
  have hdescent : baseEnd_674897 < baseStart_674897 := by decide
  rcases family_descends (prefixWord ++ tailWord_674897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674911 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 2, 2, 2]
def baseStart_674911 : Nat := 118140960795 + 674911 * 2 ^ 59
def prefixEnd_674911 : Nat := 4983230072969 + 3 ^ 40 * 674911 * 2
def baseEnd_674911 : Nat := 346553742006714141308647

theorem tailTrace_674911 : CollatzResearch.WordTrace tailWord_674911 prefixEnd_674911 346553742006714141308647 := by
  unfold tailWord_674911
  simp only [CollatzResearch.WordTrace]
  refine ⟨24616026457920187467144587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16410684305280124978096391 24616026457920187467144587)
  ·
    refine ⟨36924039686880281200716881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24616026457920187467144587 36924039686880281200716881)
    ·
      refine ⟨27693029765160210900537661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36924039686880281200716881 27693029765160210900537661)
      ·
        refine ⟨10384886161935079087701623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27693029765160210900537661 10384886161935079087701623)
        ·
          refine ⟨15577329242902618631552435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384886161935079087701623 15577329242902618631552435)
          ·
            refine ⟨23365993864353927947328653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15577329242902618631552435 23365993864353927947328653)
            ·
              refine ⟨8762247699132722980248245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23365993864353927947328653 8762247699132722980248245)
              ·
                refine ⟨821460721793692779398273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8762247699132722980248245 821460721793692779398273)
                ·
                  refine ⟨616095541345269584548705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 821460721793692779398273 616095541345269584548705)
                  ·
                    refine ⟨462071656008952188411529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616095541345269584548705 462071656008952188411529)
                    ·
                      refine ⟨346553742006714141308647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462071656008952188411529 346553742006714141308647)
                      ·
                        rfl

theorem cell23_674911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_674911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674911 prefixEnd_674911 := by exact prefixLift 674911
  have htrace : WordTrace (prefixWord ++ tailWord_674911) baseStart_674911 baseEnd_674911 := by
    simpa [prefixWord, tailWord_674911, baseEnd_674911] using wordTrace_append hprefix tailTrace_674911
  have hstable : (prefixWord ++ tailWord_674911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674911).length < 2 ^ (prefixWord ++ tailWord_674911).sum := by decide
  have hdescent : baseEnd_674911 < baseStart_674911 := by decide
  rcases family_descends (prefixWord ++ tailWord_674911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674917 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 7]
def baseStart_674917 : Nat := 118140960795 + 674917 * 2 ^ 59
def prefixEnd_674917 : Nat := 4983230072969 + 3 ^ 40 * 674917 * 2
def baseEnd_674917 : Nat := 38506313654515679759291

theorem tailTrace_674917 : CollatzResearch.WordTrace tailWord_674917 prefixEnd_674917 38506313654515679759291 := by
  unfold tailWord_674917
  simp only [CollatzResearch.WordTrace]
  refine ⟨24616245295898450491863005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16410830197265633661242003 24616245295898450491863005)
  ·
    refine ⟨9231091985961918934448627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24616245295898450491863005 9231091985961918934448627)
    ·
      refine ⟨13846637978942878401672941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9231091985961918934448627 13846637978942878401672941)
      ·
        refine ⟨5192489242103579400627353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13846637978942878401672941 5192489242103579400627353)
        ·
          refine ⟨3894366931577684550470515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5192489242103579400627353 3894366931577684550470515)
          ·
            refine ⟨5841550397366526825705773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894366931577684550470515 5841550397366526825705773)
            ·
              refine ⟨2190581399012447559639665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5841550397366526825705773 2190581399012447559639665)
              ·
                refine ⟨1642936049259335669729749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190581399012447559639665 1642936049259335669729749)
                ·
                  refine ⟨38506313654515679759291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1642936049259335669729749 38506313654515679759291)
                  ·
                    rfl

theorem cell23_674917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_674917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674917 prefixEnd_674917 := by exact prefixLift 674917
  have htrace : WordTrace (prefixWord ++ tailWord_674917) baseStart_674917 baseEnd_674917 := by
    simpa [prefixWord, tailWord_674917, baseEnd_674917] using wordTrace_append hprefix tailTrace_674917
  have hstable : (prefixWord ++ tailWord_674917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674917).length < 2 ^ (prefixWord ++ tailWord_674917).sum := by decide
  have hdescent : baseEnd_674917 < baseStart_674917 := by decide
  rcases family_descends (prefixWord ++ tailWord_674917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674927 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_674927 : Nat := 118140960795 + 674927 * 2 ^ 59
def prefixEnd_674927 : Nat := 4983230072969 + 3 ^ 40 * 674927 * 2
def baseEnd_674927 : Nat := 346561957697186078708573

theorem tailTrace_674927 : CollatzResearch.WordTrace tailWord_674927 prefixEnd_674927 346561957697186078708573 := by
  unfold tailWord_674927
  simp only [CollatzResearch.WordTrace]
  refine ⟨24616610025862222199727035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16411073350574814799818023 24616610025862222199727035)
  ·
    refine ⟨36924915038793333299590553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24616610025862222199727035 36924915038793333299590553)
    ·
      refine ⟨27693686279094999974692915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36924915038793333299590553 27693686279094999974692915)
      ·
        refine ⟨41540529418642499962039373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27693686279094999974692915 41540529418642499962039373)
        ·
          refine ⟨15577698531990937485764765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41540529418642499962039373 15577698531990937485764765)
          ·
            refine ⟨5841636949496601557161787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15577698531990937485764765 5841636949496601557161787)
            ·
              refine ⟨8762455424244902335742681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841636949496601557161787 8762455424244902335742681)
              ·
                refine ⟨6571841568183676751807011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762455424244902335742681 6571841568183676751807011)
                ·
                  refine ⟨9857762352275515127710517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571841568183676751807011 9857762352275515127710517)
                  ·
                    refine ⟨924165220525829543222861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9857762352275515127710517 924165220525829543222861)
                    ·
                      refine ⟨346561957697186078708573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924165220525829543222861 346561957697186078708573)
                      ·
                        rfl

theorem cell23_674927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_674927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674927 prefixEnd_674927 := by exact prefixLift 674927
  have htrace : WordTrace (prefixWord ++ tailWord_674927) baseStart_674927 baseEnd_674927 := by
    simpa [prefixWord, tailWord_674927, baseEnd_674927] using wordTrace_append hprefix tailTrace_674927
  have hstable : (prefixWord ++ tailWord_674927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674927).length < 2 ^ (prefixWord ++ tailWord_674927).sum := by decide
  have hdescent : baseEnd_674927 < baseStart_674927 := by decide
  rcases family_descends (prefixWord ++ tailWord_674927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674945 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_674945 : Nat := 118140960795 + 674945 * 2 ^ 59
def prefixEnd_674945 : Nat := 4983230072969 + 3 ^ 40 * 674945 * 2
def baseEnd_674945 : Nat := 346571200348967008283491

theorem tailTrace_674945 : CollatzResearch.WordTrace tailWord_674945 prefixEnd_674945 346571200348967008283491 := by
  unfold tailWord_674945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617266539797011273882289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16411511026531340849254859 24617266539797011273882289)
  ·
    refine ⟨18462949904847758455411717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24617266539797011273882289 18462949904847758455411717)
    ·
      refine ⟨3461803107158954710389697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18462949904847758455411717 3461803107158954710389697)
      ·
        refine ⟨2596352330369216032792273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3461803107158954710389697 2596352330369216032792273)
        ·
          refine ⟨1947264247776912024594205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596352330369216032792273 1947264247776912024594205)
          ·
            refine ⟨730224092916342009222827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1947264247776912024594205 730224092916342009222827)
            ·
              refine ⟨1095336139374513013834241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730224092916342009222827 1095336139374513013834241)
              ·
                refine ⟨821502104530884760375681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095336139374513013834241 821502104530884760375681)
                ·
                  refine ⟨616126578398163570281761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 821502104530884760375681 616126578398163570281761)
                  ·
                    refine ⟨462094933798622677711321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616126578398163570281761 462094933798622677711321)
                    ·
                      refine ⟨346571200348967008283491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462094933798622677711321 346571200348967008283491)
                      ·
                        rfl

theorem cell23_674945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_674945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674945 prefixEnd_674945 := by exact prefixLift 674945
  have htrace : WordTrace (prefixWord ++ tailWord_674945) baseStart_674945 baseEnd_674945 := by
    simpa [prefixWord, tailWord_674945, baseEnd_674945] using wordTrace_append hprefix tailTrace_674945
  have hstable : (prefixWord ++ tailWord_674945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674945).length < 2 ^ (prefixWord ++ tailWord_674945).sum := by decide
  have hdescent : baseEnd_674945 < baseStart_674945 := by decide
  rcases family_descends (prefixWord ++ tailWord_674945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674947 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 4, 5]
def baseStart_674947 : Nat := 118140960795 + 674947 * 2 ^ 59
def prefixEnd_674947 : Nat := 4983230072969 + 3 ^ 40 * 674947 * 2
def baseEnd_674947 : Nat := 115524075770092000152827

theorem tailTrace_674947 : CollatzResearch.WordTrace tailWord_674947 prefixEnd_674947 115524075770092000152827 := by
  unfold tailWord_674947
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617339485789765615455095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16411559657193177076970063 24617339485789765615455095)
  ·
    refine ⟨36926009228684648423182643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24617339485789765615455095 36926009228684648423182643)
    ·
      refine ⟨55389013843026972634773965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36926009228684648423182643 55389013843026972634773965)
      ·
        refine ⟨20770880191135114738040237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55389013843026972634773965 20770880191135114738040237)
        ·
          refine ⟨7789080071675668026765089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20770880191135114738040237 7789080071675668026765089)
          ·
            refine ⟨5841810053756751020073817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7789080071675668026765089 5841810053756751020073817)
            ·
              refine ⟨4381357540317563265055363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5841810053756751020073817 4381357540317563265055363)
              ·
                refine ⟨6572036310476344897583045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381357540317563265055363 6572036310476344897583045)
                ·
                  refine ⟨1232256808214314668296821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6572036310476344897583045 1232256808214314668296821)
                  ·
                    refine ⟨115524075770092000152827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1232256808214314668296821 115524075770092000152827)
                    ·
                      rfl

theorem cell23_674947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 5].length) (baseStart_674947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674947 prefixEnd_674947 := by exact prefixLift 674947
  have htrace : WordTrace (prefixWord ++ tailWord_674947) baseStart_674947 baseEnd_674947 := by
    simpa [prefixWord, tailWord_674947, baseEnd_674947] using wordTrace_append hprefix tailTrace_674947
  have hstable : (prefixWord ++ tailWord_674947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674947).length < 2 ^ (prefixWord ++ tailWord_674947).sum := by decide
  have hdescent : baseEnd_674947 < baseStart_674947 := by decide
  rcases family_descends (prefixWord ++ tailWord_674947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_674977 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_674977 : Nat := 118140960795 + 674977 * 2 ^ 59
def prefixEnd_674977 : Nat := 4983230072969 + 3 ^ 40 * 674977 * 2
def baseEnd_674977 : Nat := 115529210576636961027781

theorem tailTrace_674977 : CollatzResearch.WordTrace tailWord_674977 prefixEnd_674977 115529210576636961027781 := by
  unfold tailWord_674977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618433675681080739047185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16412289117120720492698123 24618433675681080739047185)
  ·
    refine ⟨18463825256760810554285389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24618433675681080739047185 18463825256760810554285389)
    ·
      refine ⟨6923934471285303957857021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18463825256760810554285389 6923934471285303957857021)
      ·
        refine ⟨2596475426731988984196383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6923934471285303957857021 2596475426731988984196383)
        ·
          refine ⟨3894713140097983476294575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596475426731988984196383 3894713140097983476294575)
          ·
            refine ⟨5842069710146975214441863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894713140097983476294575 5842069710146975214441863)
            ·
              refine ⟨8763104565220462821662795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842069710146975214441863 8763104565220462821662795)
              ·
                refine ⟨13144656847830694232494193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763104565220462821662795 13144656847830694232494193)
                ·
                  refine ⟨9858492635873020674370645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13144656847830694232494193 9858492635873020674370645)
                  ·
                    refine ⟨115529210576636961027781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9858492635873020674370645 115529210576636961027781)
                    ·
                      rfl

theorem cell23_674977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_674977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_674977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_674977 prefixEnd_674977 := by exact prefixLift 674977
  have htrace : WordTrace (prefixWord ++ tailWord_674977) baseStart_674977 baseEnd_674977 := by
    simpa [prefixWord, tailWord_674977, baseEnd_674977] using wordTrace_append hprefix tailTrace_674977
  have hstable : (prefixWord ++ tailWord_674977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_674977).length < 2 ^ (prefixWord ++ tailWord_674977).sum := by decide
  have hdescent : baseEnd_674977 < baseStart_674977 := by decide
  rcases family_descends (prefixWord ++ tailWord_674977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675007 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 8]
def baseStart_675007 : Nat := 118140960795 + 675007 * 2 ^ 59
def prefixEnd_675007 : Nat := 4983230072969 + 3 ^ 40 * 675007 * 2
def baseEnd_675007 : Nat := 38511448461060640634245

theorem tailTrace_675007 : CollatzResearch.WordTrace tailWord_675007 prefixEnd_675007 38511448461060640634245 := by
  unfold tailWord_675007
  simp only [CollatzResearch.WordTrace]
  refine ⟨24619527865572395862639275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16413018577048263908426183 24619527865572395862639275)
  ·
    refine ⟨36929291798358593793958913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24619527865572395862639275 36929291798358593793958913)
    ·
      refine ⟨27696968848768945345469185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36929291798358593793958913 27696968848768945345469185)
      ·
        refine ⟨20772726636576709009101889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27696968848768945345469185 20772726636576709009101889)
        ·
          refine ⟨15579544977432531756826417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20772726636576709009101889 15579544977432531756826417)
          ·
            refine ⟨11684658733074398817619813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579544977432531756826417 11684658733074398817619813)
            ·
              refine ⟨2190873512451449778303715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11684658733074398817619813 2190873512451449778303715)
              ·
                refine ⟨3286310268677174667455573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190873512451449778303715 3286310268677174667455573)
                ·
                  refine ⟨38511448461060640634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3286310268677174667455573 38511448461060640634245)
                  ·
                    rfl

theorem cell23_675007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 8].length) (baseStart_675007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675007 prefixEnd_675007 := by exact prefixLift 675007
  have htrace : WordTrace (prefixWord ++ tailWord_675007) baseStart_675007 baseEnd_675007 := by
    simpa [prefixWord, tailWord_675007, baseEnd_675007] using wordTrace_append hprefix tailTrace_675007
  have hstable : (prefixWord ++ tailWord_675007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675007).length < 2 ^ (prefixWord ++ tailWord_675007).sum := by decide
  have hdescent : baseEnd_675007 < baseStart_675007 := by decide
  rcases family_descends (prefixWord ++ tailWord_675007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675084 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_675084 : Nat := 118140960795 + 675084 * 2 ^ 59
def prefixEnd_675084 : Nat := 4983230072969 + 3 ^ 40 * 675084 * 2
def baseEnd_675084 : Nat := 115547524719980654815117

theorem tailTrace_675084 : CollatzResearch.WordTrace tailWord_675084 prefixEnd_675084 115547524719980654815117 := by
  unfold tailWord_675084
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311168143146719006596153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16414890857528958675461537 12311168143146719006596153)
  ·
    refine ⟨9233376107360039254947115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12311168143146719006596153 9233376107360039254947115)
    ·
      refine ⟨13850064161040058882420673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9233376107360039254947115 13850064161040058882420673)
      ·
        refine ⟨10387548120780044161815505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13850064161040058882420673 10387548120780044161815505)
        ·
          refine ⟨7790661090585033121361629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10387548120780044161815505 7790661090585033121361629)
          ·
            refine ⟨2921497908969387420510611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7790661090585033121361629 2921497908969387420510611)
            ·
              refine ⟨4382246863454081130765917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921497908969387420510611 4382246863454081130765917)
              ·
                refine ⟨1643342573795280424037219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4382246863454081130765917 1643342573795280424037219)
                ·
                  refine ⟨2465013860692920636055829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643342573795280424037219 2465013860692920636055829)
                  ·
                    refine ⟨115547524719980654815117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2465013860692920636055829 115547524719980654815117)
                    ·
                      rfl

theorem cell23_675084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_675084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675084 prefixEnd_675084 := by exact prefixLift 675084
  have htrace : WordTrace (prefixWord ++ tailWord_675084) baseStart_675084 baseEnd_675084 := by
    simpa [prefixWord, tailWord_675084, baseEnd_675084] using wordTrace_append hprefix tailTrace_675084
  have hstable : (prefixWord ++ tailWord_675084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675084).length < 2 ^ (prefixWord ++ tailWord_675084).sum := by decide
  have hdescent : baseEnd_675084 < baseStart_675084 := by decide
  rcases family_descends (prefixWord ++ tailWord_675084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675101 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_675101 : Nat := 118140960795 + 675101 * 2 ^ 59
def prefixEnd_675101 : Nat := 4983230072969 + 3 ^ 40 * 675101 * 2
def baseEnd_675101 : Nat := 115550434443689465977591

theorem tailTrace_675101 : CollatzResearch.WordTrace tailWord_675101 prefixEnd_675101 115550434443689465977591 := by
  unfold tailWord_675101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24622956327231849916561157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16415304218154566611040771 24622956327231849916561157)
  ·
    refine ⟨4616804311355971859355217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24622956327231849916561157 4616804311355971859355217)
    ·
      refine ⟨3462603233516978894516413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4616804311355971859355217 3462603233516978894516413)
      ·
        refine ⟨1298476212568867085443655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3462603233516978894516413 1298476212568867085443655)
        ·
          refine ⟨1947714318853300628165483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298476212568867085443655 1947714318853300628165483)
          ·
            refine ⟨2921571478279950942248225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947714318853300628165483 2921571478279950942248225)
            ·
              refine ⟨2191178608709963206686169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921571478279950942248225 2191178608709963206686169)
              ·
                refine ⟨1643383956532472405014627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191178608709963206686169 1643383956532472405014627)
                ·
                  refine ⟨2465075934798708607521941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643383956532472405014627 2465075934798708607521941)
                  ·
                    refine ⟨115550434443689465977591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2465075934798708607521941 115550434443689465977591)
                    ·
                      rfl

theorem cell23_675101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_675101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675101 prefixEnd_675101 := by exact prefixLift 675101
  have htrace : WordTrace (prefixWord ++ tailWord_675101) baseStart_675101 baseEnd_675101 := by
    simpa [prefixWord, tailWord_675101, baseEnd_675101] using wordTrace_append hprefix tailTrace_675101
  have hstable : (prefixWord ++ tailWord_675101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675101).length < 2 ^ (prefixWord ++ tailWord_675101).sum := by decide
  have hdescent : baseEnd_675101 < baseStart_675101 := by decide
  rcases family_descends (prefixWord ++ tailWord_675101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675108 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_675108 : Nat := 118140960795 + 675108 * 2 ^ 59
def prefixEnd_675108 : Nat := 4983230072969 + 3 ^ 40 * 675108 * 2
def baseEnd_675108 : Nat := 346654897695649870545241

theorem tailTrace_675108 : CollatzResearch.WordTrace tailWord_675108 prefixEnd_675108 346654897695649870545241 := by
  unfold tailWord_675108
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311605819103245056032989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16415474425470993408043985 12311605819103245056032989)
  ·
    refine ⟨4616852182163716896012371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12311605819103245056032989 4616852182163716896012371)
    ·
      refine ⟨6925278273245575344018557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616852182163716896012371 6925278273245575344018557)
      ·
        refine ⟨2596979352467090754006959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6925278273245575344018557 2596979352467090754006959)
        ·
          refine ⟨3895469028700636131010439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596979352467090754006959 3895469028700636131010439)
          ·
            refine ⟨5843203543050954196515659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895469028700636131010439 5843203543050954196515659)
            ·
              refine ⟨8764805314576431294773489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843203543050954196515659 8764805314576431294773489)
              ·
                refine ⟨6573603985932323471080117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8764805314576431294773489 6573603985932323471080117)
                ·
                  refine ⟨616275373681155325413761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6573603985932323471080117 616275373681155325413761)
                  ·
                    refine ⟨462206530260866494060321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616275373681155325413761 462206530260866494060321)
                    ·
                      refine ⟨346654897695649870545241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462206530260866494060321 346654897695649870545241)
                      ·
                        rfl

theorem cell23_675108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_675108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675108 prefixEnd_675108 := by exact prefixLift 675108
  have htrace : WordTrace (prefixWord ++ tailWord_675108) baseStart_675108 baseEnd_675108 := by
    simpa [prefixWord, tailWord_675108, baseEnd_675108] using wordTrace_append hprefix tailTrace_675108
  have hstable : (prefixWord ++ tailWord_675108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675108).length < 2 ^ (prefixWord ++ tailWord_675108).sum := by decide
  have hdescent : baseEnd_675108 < baseStart_675108 := by decide
  rcases family_descends (prefixWord ++ tailWord_675108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675125 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_675125 : Nat := 118140960795 + 675125 * 2 ^ 59
def prefixEnd_675125 : Nat := 4983230072969 + 3 ^ 40 * 675125 * 2
def baseEnd_675125 : Nat := 346663626866776304032663

theorem tailTrace_675125 : CollatzResearch.WordTrace tailWord_675125 prefixEnd_675125 346663626866776304032663 := by
  unfold tailWord_675125
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623831679144902015434829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16415887786096601343623219 24623831679144902015434829)
  ·
    refine ⟨9233936879679338255788061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24623831679144902015434829 9233936879679338255788061)
    ·
      refine ⟨3462726329879751845920523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9233936879679338255788061 3462726329879751845920523)
      ·
        refine ⟨5194089494819627768880785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462726329879751845920523 5194089494819627768880785)
        ·
          refine ⟨3895567121114720826660589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5194089494819627768880785 3895567121114720826660589)
          ·
            refine ⟨1460837670418020309997721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3895567121114720826660589 1460837670418020309997721)
            ·
              refine ⟨1095628252813515232498291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460837670418020309997721 1095628252813515232498291)
              ·
                refine ⟨1643442379220272848747437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095628252813515232498291 1643442379220272848747437)
                ·
                  refine ⟨616290892207602318280289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1643442379220272848747437 616290892207602318280289)
                  ·
                    refine ⟨462218169155701738710217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616290892207602318280289 462218169155701738710217)
                    ·
                      refine ⟨346663626866776304032663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462218169155701738710217 346663626866776304032663)
                      ·
                        rfl

theorem cell23_675125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_675125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675125 prefixEnd_675125 := by exact prefixLift 675125
  have htrace : WordTrace (prefixWord ++ tailWord_675125) baseStart_675125 baseEnd_675125 := by
    simpa [prefixWord, tailWord_675125, baseEnd_675125] using wordTrace_append hprefix tailTrace_675125
  have hstable : (prefixWord ++ tailWord_675125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675125).length < 2 ^ (prefixWord ++ tailWord_675125).sum := by decide
  have hdescent : baseEnd_675125 < baseStart_675125 := by decide
  rcases family_descends (prefixWord ++ tailWord_675125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675151 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 7, 3, 2]
def baseStart_675151 : Nat := 118140960795 + 675151 * 2 ^ 59
def prefixEnd_675151 : Nat := 4983230072969 + 3 ^ 40 * 675151 * 2
def baseEnd_675151 : Nat := 346676977363793202307543

theorem tailTrace_675151 : CollatzResearch.WordTrace tailWord_675151 prefixEnd_675151 346676977363793202307543 := by
  unfold tailWord_675151
  simp only [CollatzResearch.WordTrace]
  refine ⟨24624779977050708455881307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16416519984700472303920871 24624779977050708455881307)
  ·
    refine ⟨36937169965576062683821961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24624779977050708455881307 36937169965576062683821961)
    ·
      refine ⟨27702877474182047012866471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36937169965576062683821961 27702877474182047012866471)
      ·
        refine ⟨41554316211273070519299707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27702877474182047012866471 41554316211273070519299707)
        ·
          refine ⟨62331474316909605778949561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41554316211273070519299707 62331474316909605778949561)
          ·
            refine ⟨46748605737682204334212171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62331474316909605778949561 46748605737682204334212171)
            ·
              refine ⟨70122908606523306501318257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46748605737682204334212171 70122908606523306501318257)
              ·
                refine ⟨52592181454892479875988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70122908606523306501318257 52592181454892479875988693)
                ·
                  refine ⟨1232629252849042497093485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 52592181454892479875988693 1232629252849042497093485)
                  ·
                    refine ⟨462235969818390936410057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232629252849042497093485 462235969818390936410057)
                    ·
                      refine ⟨346676977363793202307543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462235969818390936410057 346676977363793202307543)
                      ·
                        rfl

theorem cell23_675151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3, 2].length) (baseStart_675151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675151 prefixEnd_675151 := by exact prefixLift 675151
  have htrace : WordTrace (prefixWord ++ tailWord_675151) baseStart_675151 baseEnd_675151 := by
    simpa [prefixWord, tailWord_675151, baseEnd_675151] using wordTrace_append hprefix tailTrace_675151
  have hstable : (prefixWord ++ tailWord_675151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675151).length < 2 ^ (prefixWord ++ tailWord_675151).sum := by decide
  have hdescent : baseEnd_675151 < baseStart_675151 := by decide
  rcases family_descends (prefixWord ++ tailWord_675151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675165 : List Nat := [1, 4, 5, 1, 1, 2, 9]
def baseStart_675165 : Nat := 118140960795 + 675165 * 2 ^ 59
def prefixEnd_675165 : Nat := 4983230072969 + 3 ^ 40 * 675165 * 2
def baseEnd_675165 : Nat := 4280051433246372191759

theorem tailTrace_675165 : CollatzResearch.WordTrace tailWord_675165 prefixEnd_675165 4280051433246372191759 := by
  unfold tailWord_675165
  simp only [CollatzResearch.WordTrace]
  refine ⟨24625290598999988846890949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16416860399333325897927299 24625290598999988846890949)
  ·
    refine ⟨4617241987312497908792053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24625290598999988846890949 4617241987312497908792053)
    ·
      refine ⟨432866436310546678949255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4617241987312497908792053 432866436310546678949255)
      ·
        refine ⟨649299654465820018423883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432866436310546678949255 649299654465820018423883)
        ·
          refine ⟨973949481698730027635825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649299654465820018423883 973949481698730027635825)
          ·
            refine ⟨730462111274047520726869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 973949481698730027635825 730462111274047520726869)
            ·
              refine ⟨4280051433246372191759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 730462111274047520726869 4280051433246372191759)
              ·
                rfl

theorem cell23_675165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 9].length) (baseStart_675165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675165 prefixEnd_675165 := by exact prefixLift 675165
  have htrace : WordTrace (prefixWord ++ tailWord_675165) baseStart_675165 baseEnd_675165 := by
    simpa [prefixWord, tailWord_675165, baseEnd_675165] using wordTrace_append hprefix tailTrace_675165
  have hstable : (prefixWord ++ tailWord_675165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675165).length < 2 ^ (prefixWord ++ tailWord_675165).sum := by decide
  have hdescent : baseEnd_675165 < baseStart_675165 := by decide
  rcases family_descends (prefixWord ++ tailWord_675165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675184 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_675184 : Nat := 118140960795 + 675184 * 2 ^ 59
def prefixEnd_675184 : Nat := 4983230072969 + 3 ^ 40 * 675184 * 2
def baseEnd_675184 : Nat := 346693922225391573194891

theorem tailTrace_675184 : CollatzResearch.WordTrace tailWord_675184 prefixEnd_675184 346693922225391573194891 := by
  unfold tailWord_675184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12312991792965577545916303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16417322390620770061221737 12312991792965577545916303)
  ·
    refine ⟨18469487689448366318874455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12312991792965577545916303 18469487689448366318874455)
    ·
      refine ⟨27704231534172549478311683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18469487689448366318874455 27704231534172549478311683)
      ·
        refine ⟨41556347301258824217467525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27704231534172549478311683 41556347301258824217467525)
        ·
          refine ⟨7791815118986029540775161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41556347301258824217467525 7791815118986029540775161)
          ·
            refine ⟨5843861339239522155581371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7791815118986029540775161 5843861339239522155581371)
            ·
              refine ⟨8765792008859283233372057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843861339239522155581371 8765792008859283233372057)
              ·
                refine ⟨6574344006644462425029043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765792008859283233372057 6574344006644462425029043)
                ·
                  refine ⟨9861516009966693637543565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574344006644462425029043 9861516009966693637543565)
                  ·
                    refine ⟨3698068503737510114078837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9861516009966693637543565 3698068503737510114078837)
                    ·
                      refine ⟨346693922225391573194891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3698068503737510114078837 346693922225391573194891)
                      ·
                        rfl

theorem cell23_675184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_675184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675184 prefixEnd_675184 := by exact prefixLift 675184
  have htrace : WordTrace (prefixWord ++ tailWord_675184) baseStart_675184 baseEnd_675184 := by
    simpa [prefixWord, tailWord_675184, baseEnd_675184] using wordTrace_append hprefix tailTrace_675184
  have hstable : (prefixWord ++ tailWord_675184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675184).length < 2 ^ (prefixWord ++ tailWord_675184).sum := by decide
  have hdescent : baseEnd_675184 < baseStart_675184 := by decide
  rcases family_descends (prefixWord ++ tailWord_675184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675202 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_675202 : Nat := 118140960795 + 675202 * 2 ^ 59
def prefixEnd_675202 : Nat := 4983230072969 + 3 ^ 40 * 675202 * 2
def baseEnd_675202 : Nat := 346703164877172502769809

theorem tailTrace_675202 : CollatzResearch.WordTrace tailWord_675202 prefixEnd_675202 346703164877172502769809 := by
  unfold tailWord_675202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156660024966486041496965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16417760066577296110658573 6156660024966486041496965)
  ·
    refine ⟨1154373754681216132780681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6156660024966486041496965 1154373754681216132780681)
    ·
      refine ⟨865780316010912099585511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154373754681216132780681 865780316010912099585511)
      ·
        refine ⟨1298670474016368149378267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865780316010912099585511 1298670474016368149378267)
        ·
          refine ⟨1948005711024552224067401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298670474016368149378267 1948005711024552224067401)
          ·
            refine ⟨1461004283268414168050551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948005711024552224067401 1461004283268414168050551)
            ·
              refine ⟨2191506424902621252075827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461004283268414168050551 2191506424902621252075827)
              ·
                refine ⟨3287259637353931878113741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191506424902621252075827 3287259637353931878113741)
                ·
                  refine ⟨1232722364007724454292653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3287259637353931878113741 1232722364007724454292653)
                  ·
                    refine ⟨462270886502896670359745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1232722364007724454292653 462270886502896670359745)
                    ·
                      refine ⟨346703164877172502769809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462270886502896670359745 346703164877172502769809)
                      ·
                        rfl

theorem cell23_675202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_675202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675202 prefixEnd_675202 := by exact prefixLift 675202
  have htrace : WordTrace (prefixWord ++ tailWord_675202) baseStart_675202 baseEnd_675202 := by
    simpa [prefixWord, tailWord_675202, baseEnd_675202] using wordTrace_append hprefix tailTrace_675202
  have hstable : (prefixWord ++ tailWord_675202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675202).length < 2 ^ (prefixWord ++ tailWord_675202).sum := by decide
  have hdescent : baseEnd_675202 < baseStart_675202 := by decide
  rcases family_descends (prefixWord ++ tailWord_675202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675268 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_675268 : Nat := 118140960795 + 675268 * 2 ^ 59
def prefixEnd_675268 : Nat := 4983230072969 + 3 ^ 40 * 675268 * 2
def baseEnd_675268 : Nat := 115579018200123081514835

theorem tailTrace_675268 : CollatzResearch.WordTrace tailWord_675268 prefixEnd_675268 115579018200123081514835 := by
  unfold tailWord_675268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314523658813418718945229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16419364878417891625260305 12314523658813418718945229)
  ·
    refine ⟨4617946372055032019604461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12314523658813418718945229 4617946372055032019604461)
    ·
      refine ⟨1731729889520637007351673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4617946372055032019604461 1731729889520637007351673)
      ·
        refine ⟨1298797417140477755513755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731729889520637007351673 1298797417140477755513755)
        ·
          refine ⟨1948196125710716633270633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298797417140477755513755 1948196125710716633270633)
          ·
            refine ⟨1461147094283037474952975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948196125710716633270633 1461147094283037474952975)
            ·
              refine ⟨2191720641424556212429463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461147094283037474952975 2191720641424556212429463)
              ·
                refine ⟨3287580962136834318644195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191720641424556212429463 3287580962136834318644195)
                ·
                  refine ⟨4931371443205251477966293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287580962136834318644195 4931371443205251477966293)
                  ·
                    refine ⟨115579018200123081514835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4931371443205251477966293 115579018200123081514835)
                    ·
                      rfl

theorem cell23_675268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_675268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675268 prefixEnd_675268 := by exact prefixLift 675268
  have htrace : WordTrace (prefixWord ++ tailWord_675268) baseStart_675268 baseEnd_675268 := by
    simpa [prefixWord, tailWord_675268, baseEnd_675268] using wordTrace_append hprefix tailTrace_675268
  have hstable : (prefixWord ++ tailWord_675268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675268).length < 2 ^ (prefixWord ++ tailWord_675268).sum := by decide
  have hdescent : baseEnd_675268 < baseStart_675268 := by decide
  rcases family_descends (prefixWord ++ tailWord_675268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675271 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_675271 : Nat := 118140960795 + 675271 * 2 ^ 59
def prefixEnd_675271 : Nat := 4983230072969 + 3 ^ 40 * 675271 * 2
def baseEnd_675271 : Nat := 346738595042332732806991

theorem tailTrace_675271 : CollatzResearch.WordTrace tailWord_675271 prefixEnd_675271 346738595042332732806991 := by
  unfold tailWord_675271
  simp only [CollatzResearch.WordTrace]
  refine ⟨24629156736615968950249667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16419437824410645966833111 24629156736615968950249667)
  ·
    refine ⟨36943735104923953425374501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24629156736615968950249667 36943735104923953425374501)
    ·
      refine ⟨6926950332173241267257719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36943735104923953425374501 6926950332173241267257719)
      ·
        refine ⟨10390425498259861900886579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6926950332173241267257719 10390425498259861900886579)
        ·
          refine ⟨15585638247389792851329869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390425498259861900886579 15585638247389792851329869)
          ·
            refine ⟨5844614342771172319248701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15585638247389792851329869 5844614342771172319248701)
            ·
              refine ⟨2191730378539189619718263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5844614342771172319248701 2191730378539189619718263)
              ·
                refine ⟨3287595567808784429577395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191730378539189619718263 3287595567808784429577395)
                ·
                  refine ⟨4931393351713176644366093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287595567808784429577395 4931393351713176644366093)
                  ·
                    refine ⟨1849272506892441241637285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4931393351713176644366093 1849272506892441241637285)
                    ·
                      refine ⟨346738595042332732806991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1849272506892441241637285 346738595042332732806991)
                      ·
                        rfl

theorem cell23_675271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_675271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675271 prefixEnd_675271 := by exact prefixLift 675271
  have htrace : WordTrace (prefixWord ++ tailWord_675271) baseStart_675271 baseEnd_675271 := by
    simpa [prefixWord, tailWord_675271, baseEnd_675271] using wordTrace_append hprefix tailTrace_675271
  have hstable : (prefixWord ++ tailWord_675271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675271).length < 2 ^ (prefixWord ++ tailWord_675271).sum := by decide
  have hdescent : baseEnd_675271 < baseStart_675271 := by decide
  rcases family_descends (prefixWord ++ tailWord_675271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675288 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_675288 : Nat := 118140960795 + 675288 * 2 ^ 59
def prefixEnd_675288 : Nat := 4983230072969 + 3 ^ 40 * 675288 * 2
def baseEnd_675288 : Nat := 346747324213459166294413

theorem tailTrace_675288 : CollatzResearch.WordTrace tailWord_675288 prefixEnd_675288 346747324213459166294413 := by
  unfold tailWord_675288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314888388777190426809259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16419851185036253902412345 12314888388777190426809259)
  ·
    refine ⟨18472332583165785640213889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12314888388777190426809259 18472332583165785640213889)
    ·
      refine ⟨13854249437374339230160417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18472332583165785640213889 13854249437374339230160417)
      ·
        refine ⟨10390687078030754422620313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854249437374339230160417 10390687078030754422620313)
        ·
          refine ⟨7793015308523065816965235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10390687078030754422620313 7793015308523065816965235)
          ·
            refine ⟨11689522962784598725447853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793015308523065816965235 11689522962784598725447853)
            ·
              refine ⟨4383571111044224522042945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11689522962784598725447853 4383571111044224522042945)
              ·
                refine ⟨3287678333283168391532209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383571111044224522042945 3287678333283168391532209)
                ·
                  refine ⟨2465758749962376293649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287678333283168391532209 2465758749962376293649157)
                  ·
                    refine ⟨462329765617945555059217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2465758749962376293649157 462329765617945555059217)
                    ·
                      refine ⟨346747324213459166294413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462329765617945555059217 346747324213459166294413)
                      ·
                        rfl

theorem cell23_675288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_675288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675288 prefixEnd_675288 := by exact prefixLift 675288
  have htrace : WordTrace (prefixWord ++ tailWord_675288) baseStart_675288 baseEnd_675288 := by
    simpa [prefixWord, tailWord_675288, baseEnd_675288] using wordTrace_append hprefix tailTrace_675288
  have hstable : (prefixWord ++ tailWord_675288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675288).length < 2 ^ (prefixWord ++ tailWord_675288).sum := by decide
  have hdescent : baseEnd_675288 < baseStart_675288 := by decide
  rcases family_descends (prefixWord ++ tailWord_675288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675311 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 6]
def baseStart_675311 : Nat := 118140960795 + 675311 * 2 ^ 59
def prefixEnd_675311 : Nat := 4983230072969 + 3 ^ 40 * 675311 * 2
def baseEnd_675311 : Nat := 38528792696501397367423

theorem tailTrace_675311 : CollatzResearch.WordTrace tailWord_675311 prefixEnd_675311 38528792696501397367423 := by
  unfold tailWord_675311
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630615656471055781705787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16420410437647370521137191 24630615656471055781705787)
  ·
    refine ⟨36945923484706583672558681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24630615656471055781705787 36945923484706583672558681)
    ·
      refine ⟨27709442613529937754419011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36945923484706583672558681 27709442613529937754419011)
      ·
        refine ⟨41564163920294906631628517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27709442613529937754419011 41564163920294906631628517)
        ·
          refine ⟨7793280735055294993430347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41564163920294906631628517 7793280735055294993430347)
          ·
            refine ⟨11689921102582942490145521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7793280735055294993430347 11689921102582942490145521)
            ·
              refine ⟨8767440826937206867609141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11689921102582942490145521 8767440826937206867609141)
              ·
                refine ⟨821947577525363143838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8767440826937206867609141 821947577525363143838357)
                ·
                  refine ⟨38528792696501397367423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 821947577525363143838357 38528792696501397367423)
                  ·
                    rfl

theorem cell23_675311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 6].length) (baseStart_675311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675311 prefixEnd_675311 := by exact prefixLift 675311
  have htrace : WordTrace (prefixWord ++ tailWord_675311) baseStart_675311 baseEnd_675311 := by
    simpa [prefixWord, tailWord_675311, baseEnd_675311] using wordTrace_append hprefix tailTrace_675311
  have hstable : (prefixWord ++ tailWord_675311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675311).length < 2 ^ (prefixWord ++ tailWord_675311).sum := by decide
  have hdescent : baseEnd_675311 < baseStart_675311 := by decide
  rcases family_descends (prefixWord ++ tailWord_675311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675321 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_675321 : Nat := 118140960795 + 675321 * 2 ^ 59
def prefixEnd_675321 : Nat := 4983230072969 + 3 ^ 40 * 675321 * 2
def baseEnd_675321 : Nat := 346764269075057537181761

theorem tailTrace_675321 : CollatzResearch.WordTrace tailWord_675321 prefixEnd_675321 346764269075057537181761 := by
  unfold tailWord_675321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630980386434827489569817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16420653590956551659713211 24630980386434827489569817)
  ·
    refine ⟨18473235289826120617177363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24630980386434827489569817 18473235289826120617177363)
    ·
      refine ⟨27709852934739180925766045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18473235289826120617177363 27709852934739180925766045)
      ·
        refine ⟨10391194850527192847162267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27709852934739180925766045 10391194850527192847162267)
        ·
          refine ⟨15586792275790789270743401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391194850527192847162267 15586792275790789270743401)
          ·
            refine ⟨11690094206843091953057551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15586792275790789270743401 11690094206843091953057551)
            ·
              refine ⟨17535141310264637929586327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11690094206843091953057551 17535141310264637929586327)
              ·
                refine ⟨26302711965396956894379491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17535141310264637929586327 26302711965396956894379491)
                ·
                  refine ⟨39454067948095435341569237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26302711965396956894379491 39454067948095435341569237)
                  ·
                    refine ⟨924704717533486765818029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39454067948095435341569237 924704717533486765818029)
                    ·
                      refine ⟨346764269075057537181761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924704717533486765818029 346764269075057537181761)
                      ·
                        rfl

theorem cell23_675321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_675321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675321 prefixEnd_675321 := by exact prefixLift 675321
  have htrace : WordTrace (prefixWord ++ tailWord_675321) baseStart_675321 baseEnd_675321 := by
    simpa [prefixWord, tailWord_675321, baseEnd_675321] using wordTrace_append hprefix tailTrace_675321
  have hstable : (prefixWord ++ tailWord_675321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675321).length < 2 ^ (prefixWord ++ tailWord_675321).sum := by decide
  have hdescent : baseEnd_675321 < baseStart_675321 := by decide
  rcases family_descends (prefixWord ++ tailWord_675321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675412 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_675412 : Nat := 118140960795 + 675412 * 2 ^ 59
def prefixEnd_675412 : Nat := 4983230072969 + 3 ^ 40 * 675412 * 2
def baseEnd_675412 : Nat := 346810995814616681143843

theorem tailTrace_675412 : CollatzResearch.WordTrace tailWord_675412 prefixEnd_675412 346810995814616681143843 := by
  unfold tailWord_675412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12317149714552575015566245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16422866286070100020754993 12317149714552575015566245)
  ·
    refine ⟨2309465571478607815418671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12317149714552575015566245 2309465571478607815418671)
    ·
      refine ⟨3464198357217911723128007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309465571478607815418671 3464198357217911723128007)
      ·
        refine ⟨5196297535826867584692011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464198357217911723128007 5196297535826867584692011)
        ·
          refine ⟨7794446303740301377038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196297535826867584692011 7794446303740301377038017)
          ·
            refine ⟨5845834727805226032778513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7794446303740301377038017 5845834727805226032778513)
            ·
              refine ⟨4384376045853919524583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5845834727805226032778513 4384376045853919524583885)
              ·
                refine ⟨1644141017195219821718957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4384376045853919524583885 1644141017195219821718957)
                ·
                  refine ⟨616552881448207433144609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1644141017195219821718957 616552881448207433144609)
                  ·
                    refine ⟨462414661086155574858457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616552881448207433144609 462414661086155574858457)
                    ·
                      refine ⟨346810995814616681143843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462414661086155574858457 346810995814616681143843)
                      ·
                        rfl

theorem cell23_675412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_675412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675412 prefixEnd_675412 := by exact prefixLift 675412
  have htrace : WordTrace (prefixWord ++ tailWord_675412) baseStart_675412 baseEnd_675412 := by
    simpa [prefixWord, tailWord_675412, baseEnd_675412] using wordTrace_append hprefix tailTrace_675412
  have hstable : (prefixWord ++ tailWord_675412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675412).length < 2 ^ (prefixWord ++ tailWord_675412).sum := by decide
  have hdescent : baseEnd_675412 < baseStart_675412 := by decide
  rcases family_descends (prefixWord ++ tailWord_675412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675446 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_675446 : Nat := 118140960795 + 675446 * 2 ^ 59
def prefixEnd_675446 : Nat := 4983230072969 + 3 ^ 40 * 675446 * 2
def baseEnd_675446 : Nat := 346828454156869548118687

theorem tailTrace_675446 : CollatzResearch.WordTrace tailWord_675446 prefixEnd_675446 346828454156869548118687 := by
  unfold tailWord_675446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539721219436373364866887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16423693007321315891913461 1539721219436373364866887)
  ·
    refine ⟨2309581829154560047300331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1539721219436373364866887 2309581829154560047300331)
    ·
      refine ⟨3464372743731840070950497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309581829154560047300331 3464372743731840070950497)
      ·
        refine ⟨2598279557798880053212873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464372743731840070950497 2598279557798880053212873)
        ·
          refine ⟨1948709668349160039909655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598279557798880053212873 1948709668349160039909655)
          ·
            refine ⟨2923064502523740059864483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948709668349160039909655 2923064502523740059864483)
            ·
              refine ⟨4384596753785610089796725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923064502523740059864483 4384596753785610089796725)
              ·
                refine ⟨411055945667400945918443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4384596753785610089796725 411055945667400945918443)
                ·
                  refine ⟨616583918501101418877665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411055945667400945918443 616583918501101418877665)
                  ·
                    refine ⟨462437938875826064158249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616583918501101418877665 462437938875826064158249)
                    ·
                      refine ⟨346828454156869548118687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462437938875826064158249 346828454156869548118687)
                      ·
                        rfl

theorem cell23_675446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_675446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675446 prefixEnd_675446 := by exact prefixLift 675446
  have htrace : WordTrace (prefixWord ++ tailWord_675446) baseStart_675446 baseEnd_675446 := by
    simpa [prefixWord, tailWord_675446, baseEnd_675446] using wordTrace_append hprefix tailTrace_675446
  have hstable : (prefixWord ++ tailWord_675446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675446).length < 2 ^ (prefixWord ++ tailWord_675446).sum := by decide
  have hdescent : baseEnd_675446 < baseStart_675446 := by decide
  rcases family_descends (prefixWord ++ tailWord_675446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675479 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_675479 : Nat := 118140960795 + 675479 * 2 ^ 59
def prefixEnd_675479 : Nat := 4983230072969 + 3 ^ 40 * 675479 * 2
def baseEnd_675479 : Nat := 346845399018467919006035

theorem tailTrace_675479 : CollatzResearch.WordTrace tailWord_675479 prefixEnd_675479 346845399018467919006035 := by
  unfold tailWord_675479
  simp only [CollatzResearch.WordTrace]
  refine ⟨24636743119862420473821491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16424495413241613649214327 24636743119862420473821491)
  ·
    refine ⟨36955114679793630710732237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24636743119862420473821491 36955114679793630710732237)
    ·
      refine ⟨13858168004922611516524589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36955114679793630710732237 13858168004922611516524589)
      ·
        refine ⟨5196813001845979318696721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13858168004922611516524589 5196813001845979318696721)
        ·
          refine ⟨3897609751384484489022541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5196813001845979318696721 3897609751384484489022541)
          ·
            refine ⟨1461603656769181683383453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3897609751384484489022541 1461603656769181683383453)
            ·
              refine ⟨548101371288443131268795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1461603656769181683383453 548101371288443131268795)
              ·
                refine ⟨822152056932664696903193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548101371288443131268795 822152056932664696903193)
                ·
                  refine ⟨616614042699498522677395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822152056932664696903193 616614042699498522677395)
                  ·
                    refine ⟨924921064049247784016093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 616614042699498522677395 924921064049247784016093)
                    ·
                      refine ⟨346845399018467919006035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 924921064049247784016093 346845399018467919006035)
                      ·
                        rfl

theorem cell23_675479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_675479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675479 prefixEnd_675479 := by exact prefixLift 675479
  have htrace : WordTrace (prefixWord ++ tailWord_675479) baseStart_675479 baseEnd_675479 := by
    simpa [prefixWord, tailWord_675479, baseEnd_675479] using wordTrace_append hprefix tailTrace_675479
  have hstable : (prefixWord ++ tailWord_675479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675479).length < 2 ^ (prefixWord ++ tailWord_675479).sum := by decide
  have hdescent : baseEnd_675479 < baseStart_675479 := by decide
  rcases family_descends (prefixWord ++ tailWord_675479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675489 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_675489 : Nat := 118140960795 + 675489 * 2 ^ 59
def prefixEnd_675489 : Nat := 4983230072969 + 3 ^ 40 * 675489 * 2
def baseEnd_675489 : Nat := 346850533825012879880989

theorem tailTrace_675489 : CollatzResearch.WordTrace tailWord_675489 prefixEnd_675489 346850533825012879880989 := by
  unfold tailWord_675489
  simp only [CollatzResearch.WordTrace]
  refine ⟨24637107849826192181685521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16424738566550794787790347 24637107849826192181685521)
  ·
    refine ⟨18477830887369644136264141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24637107849826192181685521 18477830887369644136264141)
    ·
      refine ⟨6929186582763616551099053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18477830887369644136264141 6929186582763616551099053)
      ·
        refine ⟨2598444968536356206662145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6929186582763616551099053 2598444968536356206662145)
        ·
          refine ⟨1948833726402267154996609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598444968536356206662145 1948833726402267154996609)
          ·
            refine ⟨1461625294801700366247457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948833726402267154996609 1461625294801700366247457)
            ·
              refine ⟨1096218971101275274685593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461625294801700366247457 1096218971101275274685593)
              ·
                refine ⟨822164228325956456014195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096218971101275274685593 822164228325956456014195)
                ·
                  refine ⟨1233246342488934684021293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822164228325956456014195 1233246342488934684021293)
                  ·
                    refine ⟨462467378433350506507985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1233246342488934684021293 462467378433350506507985)
                    ·
                      refine ⟨346850533825012879880989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462467378433350506507985 346850533825012879880989)
                      ·
                        rfl

theorem cell23_675489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_675489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675489 prefixEnd_675489 := by exact prefixLift 675489
  have htrace : WordTrace (prefixWord ++ tailWord_675489) baseStart_675489 baseEnd_675489 := by
    simpa [prefixWord, tailWord_675489, baseEnd_675489] using wordTrace_append hprefix tailTrace_675489
  have hstable : (prefixWord ++ tailWord_675489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675489).length < 2 ^ (prefixWord ++ tailWord_675489).sum := by decide
  have hdescent : baseEnd_675489 < baseStart_675489 := by decide
  rcases family_descends (prefixWord ++ tailWord_675489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675565 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_675565 : Nat := 118140960795 + 675565 * 2 ^ 59
def prefixEnd_675565 : Nat := 4983230072969 + 3 ^ 40 * 675565 * 2
def baseEnd_675565 : Nat := 346889558354754582530639

theorem tailTrace_675565 : CollatzResearch.WordTrace tailWord_675565 prefixEnd_675565 346889558354754582530639 := by
  unfold tailWord_675565
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639879797550857161452149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16426586531700571440968099 24639879797550857161452149)
  ·
    refine ⟨2309988731020392858886139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24639879797550857161452149 2309988731020392858886139)
    ·
      refine ⟨3464983096530589288329209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309988731020392858886139 3464983096530589288329209)
      ·
        refine ⟨2598737322397941966246907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3464983096530589288329209 2598737322397941966246907)
        ·
          refine ⟨3898105983596912949370361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598737322397941966246907 3898105983596912949370361)
          ·
            refine ⟨2923579487697684712027771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898105983596912949370361 2923579487697684712027771)
            ·
              refine ⟨4385369231546527068041657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923579487697684712027771 4385369231546527068041657)
              ·
                refine ⟨3289026923659895301031243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4385369231546527068041657 3289026923659895301031243)
                ·
                  refine ⟨4933540385489842951546865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289026923659895301031243 4933540385489842951546865)
                  ·
                    refine ⟨3700155289117382213660149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4933540385489842951546865 3700155289117382213660149)
                    ·
                      refine ⟨346889558354754582530639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3700155289117382213660149 346889558354754582530639)
                      ·
                        rfl

theorem cell23_675565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_675565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675565 prefixEnd_675565 := by exact prefixLift 675565
  have htrace : WordTrace (prefixWord ++ tailWord_675565) baseStart_675565 baseEnd_675565 := by
    simpa [prefixWord, tailWord_675565, baseEnd_675565] using wordTrace_append hprefix tailTrace_675565
  have hstable : (prefixWord ++ tailWord_675565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675565).length < 2 ^ (prefixWord ++ tailWord_675565).sum := by decide
  have hdescent : baseEnd_675565 < baseStart_675565 := by decide
  rcases family_descends (prefixWord ++ tailWord_675565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675575 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_675575 : Nat := 118140960795 + 675575 * 2 ^ 59
def prefixEnd_675575 : Nat := 4983230072969 + 3 ^ 40 * 675575 * 2
def baseEnd_675575 : Nat := 346894693161299543405593

theorem tailTrace_675575 : CollatzResearch.WordTrace tailWord_675575 prefixEnd_675575 346894693161299543405593 := by
  unfold tailWord_675575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24640244527514628869316179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16426829685009752579544119 24640244527514628869316179)
  ·
    refine ⟨36960366791271943303974269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24640244527514628869316179 36960366791271943303974269)
    ·
      refine ⟨13860137546726978738990351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36960366791271943303974269 13860137546726978738990351)
      ·
        refine ⟨20790206320090468108485527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860137546726978738990351 20790206320090468108485527)
        ·
          refine ⟨31185309480135702162728291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20790206320090468108485527 31185309480135702162728291)
          ·
            refine ⟨46777964220203553244092437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31185309480135702162728291 46777964220203553244092437)
            ·
              refine ⟨2192717072822041558316833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46777964220203553244092437 2192717072822041558316833)
              ·
                refine ⟨1644537804616531168737625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2192717072822041558316833 1644537804616531168737625)
                ·
                  refine ⟨1233403353462398376553219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644537804616531168737625 1233403353462398376553219)
                  ·
                    refine ⟨1850105030193597564829829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233403353462398376553219 1850105030193597564829829)
                    ·
                      refine ⟨346894693161299543405593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1850105030193597564829829 346894693161299543405593)
                      ·
                        rfl

theorem cell23_675575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_675575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675575 prefixEnd_675575 := by exact prefixLift 675575
  have htrace : WordTrace (prefixWord ++ tailWord_675575) baseStart_675575 baseEnd_675575 := by
    simpa [prefixWord, tailWord_675575, baseEnd_675575] using wordTrace_append hprefix tailTrace_675575
  have hstable : (prefixWord ++ tailWord_675575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675575).length < 2 ^ (prefixWord ++ tailWord_675575).sum := by decide
  have hdescent : baseEnd_675575 < baseStart_675575 := by decide
  rcases family_descends (prefixWord ++ tailWord_675575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675578 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_675578 : Nat := 118140960795 + 675578 * 2 ^ 59
def prefixEnd_675578 : Nat := 4983230072969 + 3 ^ 40 * 675578 * 2
def baseEnd_675578 : Nat := 346896233603263031668079

theorem tailTrace_675578 : CollatzResearch.WordTrace tailWord_675578 prefixEnd_675578 346896233603263031668079 := by
  unfold tailWord_675578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160088486625940095418847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16426902631002506921116925 6160088486625940095418847)
  ·
    refine ⟨9240132729938910143128271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160088486625940095418847 9240132729938910143128271)
    ·
      refine ⟨13860199094908365214692407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9240132729938910143128271 13860199094908365214692407)
      ·
        refine ⟨20790298642362547822038611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860199094908365214692407 20790298642362547822038611)
        ·
          refine ⟨31185447963543821733057917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20790298642362547822038611 31185447963543821733057917)
          ·
            refine ⟨11694542986328933149896719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31185447963543821733057917 11694542986328933149896719)
            ·
              refine ⟨17541814479493399724845079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694542986328933149896719 17541814479493399724845079)
              ·
                refine ⟨26312721719240099587267619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17541814479493399724845079 26312721719240099587267619)
                ·
                  refine ⟨39469082578860149380901429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26312721719240099587267619 39469082578860149380901429)
                  ·
                    refine ⟨3700226491768139004459509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39469082578860149380901429 3700226491768139004459509)
                    ·
                      refine ⟨346896233603263031668079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3700226491768139004459509 346896233603263031668079)
                      ·
                        rfl

theorem cell23_675578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_675578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675578 prefixEnd_675578 := by exact prefixLift 675578
  have htrace : WordTrace (prefixWord ++ tailWord_675578) baseStart_675578 baseEnd_675578 := by
    simpa [prefixWord, tailWord_675578, baseEnd_675578] using wordTrace_append hprefix tailTrace_675578
  have hstable : (prefixWord ++ tailWord_675578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675578).length < 2 ^ (prefixWord ++ tailWord_675578).sum := by decide
  have hdescent : baseEnd_675578 < baseStart_675578 := by decide
  rcases family_descends (prefixWord ++ tailWord_675578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675592 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_675592 : Nat := 118140960795 + 675592 * 2 ^ 59
def prefixEnd_675592 : Nat := 4983230072969 + 3 ^ 40 * 675592 * 2
def baseEnd_675592 : Nat := 346903422332425976893015

theorem tailTrace_675592 : CollatzResearch.WordTrace tailWord_675592 prefixEnd_675592 346903422332425976893015 := by
  unfold tailWord_675592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320432284226520386342515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16427243045635360515123353 12320432284226520386342515)
  ·
    refine ⟨18480648426339780579513773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12320432284226520386342515 18480648426339780579513773)
    ·
      refine ⟨6930243159877417717317665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18480648426339780579513773 6930243159877417717317665)
      ·
        refine ⟨5197682369908063287988249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930243159877417717317665 5197682369908063287988249)
        ·
          refine ⟨3898261777431047465991187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197682369908063287988249 3898261777431047465991187)
          ·
            refine ⟨5847392666146571198986781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898261777431047465991187 5847392666146571198986781)
            ·
              refine ⟨2192772249804964199620043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5847392666146571198986781 2192772249804964199620043)
              ·
                refine ⟨3289158374707446299430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192772249804964199620043 3289158374707446299430065)
                ·
                  refine ⟨2466868781030584724572549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3289158374707446299430065 2466868781030584724572549)
                  ·
                    refine ⟨462537896443234635857353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2466868781030584724572549 462537896443234635857353)
                    ·
                      refine ⟨346903422332425976893015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462537896443234635857353 346903422332425976893015)
                      ·
                        rfl

theorem cell23_675592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_675592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675592 prefixEnd_675592 := by exact prefixLift 675592
  have htrace : WordTrace (prefixWord ++ tailWord_675592) baseStart_675592 baseEnd_675592 := by
    simpa [prefixWord, tailWord_675592, baseEnd_675592] using wordTrace_append hprefix tailTrace_675592
  have hstable : (prefixWord ++ tailWord_675592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675592).length < 2 ^ (prefixWord ++ tailWord_675592).sum := by decide
  have hdescent : baseEnd_675592 < baseStart_675592 := by decide
  rcases family_descends (prefixWord ++ tailWord_675592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675595 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3]
def baseStart_675595 : Nat := 118140960795 + 675595 * 2 ^ 59
def prefixEnd_675595 : Nat := 4983230072969 + 3 ^ 40 * 675595 * 2
def baseEnd_675595 : Nat := 346904962774389465155501

theorem tailTrace_675595 : CollatzResearch.WordTrace tailWord_675595 prefixEnd_675595 346904962774389465155501 := by
  unfold tailWord_675595
  simp only [CollatzResearch.WordTrace]
  refine ⟨24640973987442172285044239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16427315991628114856696159 24640973987442172285044239)
  ·
    refine ⟨36961460981163258427566359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24640973987442172285044239 36961460981163258427566359)
    ·
      refine ⟨55442191471744887641349539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36961460981163258427566359 55442191471744887641349539)
      ·
        refine ⟨83163287207617331462024309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55442191471744887641349539 83163287207617331462024309)
        ·
          refine ⟨7796558175714124824564779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83163287207617331462024309 7796558175714124824564779)
          ·
            refine ⟨11694837263571187236847169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796558175714124824564779 11694837263571187236847169)
            ·
              refine ⟨8771127947678390427635377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694837263571187236847169 8771127947678390427635377)
              ·
                refine ⟨6578345960758792820726533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8771127947678390427635377 6578345960758792820726533)
                ·
                  refine ⟨1233439867642273653886225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6578345960758792820726533 1233439867642273653886225)
                  ·
                    refine ⟨925079900731705240414669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233439867642273653886225 925079900731705240414669)
                    ·
                      refine ⟨346904962774389465155501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 925079900731705240414669 346904962774389465155501)
                      ·
                        rfl

theorem cell23_675595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 3].length) (baseStart_675595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675595 prefixEnd_675595 := by exact prefixLift 675595
  have htrace : WordTrace (prefixWord ++ tailWord_675595) baseStart_675595 baseEnd_675595 := by
    simpa [prefixWord, tailWord_675595, baseEnd_675595] using wordTrace_append hprefix tailTrace_675595
  have hstable : (prefixWord ++ tailWord_675595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675595).length < 2 ^ (prefixWord ++ tailWord_675595).sum := by decide
  have hdescent : baseEnd_675595 < baseStart_675595 := by decide
  rcases family_descends (prefixWord ++ tailWord_675595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675636 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_675636 : Nat := 118140960795 + 675636 * 2 ^ 59
def prefixEnd_675636 : Nat := 4983230072969 + 3 ^ 40 * 675636 * 2
def baseEnd_675636 : Nat := 115642005160407934914271

theorem tailTrace_675636 : CollatzResearch.WordTrace tailWord_675636 prefixEnd_675636 115642005160407934914271 := by
  unfold tailWord_675636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12321234690146818143643381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16428312920195757524857841 12321234690146818143643381)
  ·
    refine ⟨1155115752201264200966567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12321234690146818143643381 1155115752201264200966567)
    ·
      refine ⟨1732673628301896301449851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155115752201264200966567 1732673628301896301449851)
      ·
        refine ⟨2599010442452844452174777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732673628301896301449851 2599010442452844452174777)
        ·
          refine ⟨1949257831839633339131083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599010442452844452174777 1949257831839633339131083)
          ·
            refine ⟨2923886747759450008696625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949257831839633339131083 2923886747759450008696625)
            ·
              refine ⟨2192915060819587506522469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923886747759450008696625 2192915060819587506522469)
              ·
                refine ⟨411171573903672657472963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2192915060819587506522469 411171573903672657472963)
                ·
                  refine ⟨616757360855508986209445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411171573903672657472963 616757360855508986209445)
                  ·
                    refine ⟨115642005160407934914271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616757360855508986209445 115642005160407934914271)
                    ·
                      rfl

theorem cell23_675636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_675636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675636 prefixEnd_675636 := by exact prefixLift 675636
  have htrace : WordTrace (prefixWord ++ tailWord_675636) baseStart_675636 baseEnd_675636 := by
    simpa [prefixWord, tailWord_675636, baseEnd_675636] using wordTrace_append hprefix tailTrace_675636
  have hstable : (prefixWord ++ tailWord_675636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675636).length < 2 ^ (prefixWord ++ tailWord_675636).sum := by decide
  have hdescent : baseEnd_675636 < baseStart_675636 := by decide
  rcases family_descends (prefixWord ++ tailWord_675636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675692 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 4, 4]
def baseStart_675692 : Nat := 118140960795 + 675692 * 2 ^ 59
def prefixEnd_675692 : Nat := 4983230072969 + 3 ^ 40 * 675692 * 2
def baseEnd_675692 : Nat := 115651590132625195214185

theorem tailTrace_675692 : CollatzResearch.WordTrace tailWord_675692 prefixEnd_675692 115651590132625195214185 := by
  unfold tailWord_675692
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322255934045378925662665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16429674578727171900883553 12322255934045378925662665)
  ·
    refine ⟨9241691950534034194246999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12322255934045378925662665 9241691950534034194246999)
    ·
      refine ⟨13862537925801051291370499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241691950534034194246999 13862537925801051291370499)
      ·
        refine ⟨20793806888701576937055749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13862537925801051291370499 20793806888701576937055749)
        ·
          refine ⟨3898838791631545675697953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20793806888701576937055749 3898838791631545675697953)
          ·
            refine ⟨2924129093723659256773465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898838791631545675697953 2924129093723659256773465)
            ·
              refine ⟨2193096820292744442580099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924129093723659256773465 2193096820292744442580099)
              ·
                refine ⟨3289645230439116663870149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193096820292744442580099 3289645230439116663870149)
                ·
                  refine ⟨616808480707334374475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3289645230439116663870149 616808480707334374475653)
                  ·
                    refine ⟨115651590132625195214185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 616808480707334374475653 115651590132625195214185)
                    ·
                      rfl

theorem cell23_675692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_675692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675692 prefixEnd_675692 := by exact prefixLift 675692
  have htrace : WordTrace (prefixWord ++ tailWord_675692) baseStart_675692 baseEnd_675692 := by
    simpa [prefixWord, tailWord_675692, baseEnd_675692] using wordTrace_append hprefix tailTrace_675692
  have hstable : (prefixWord ++ tailWord_675692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675692).length < 2 ^ (prefixWord ++ tailWord_675692).sum := by decide
  have hdescent : baseEnd_675692 < baseStart_675692 := by decide
  rcases family_descends (prefixWord ++ tailWord_675692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675705 : List Nat := [1, 2, 1, 3, 2, 2, 4, 8]
def baseStart_675705 : Nat := 118140960795 + 675705 * 2 ^ 59
def prefixEnd_675705 : Nat := 4983230072969 + 3 ^ 40 * 675705 * 2
def baseEnd_675705 : Nat := 12850423912829038325185

theorem tailTrace_675705 : CollatzResearch.WordTrace tailWord_675705 prefixEnd_675705 12850423912829038325185 := by
  unfold tailWord_675705
  simp only [CollatzResearch.WordTrace]
  refine ⟨24644986017043661071548569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16429990678029107381032379 24644986017043661071548569)
  ·
    refine ⟨18483739512782745803661427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24644986017043661071548569 18483739512782745803661427)
    ·
      refine ⟨27725609269174118705492141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483739512782745803661427 27725609269174118705492141)
      ·
        refine ⟨10397103475940294514559553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27725609269174118705492141 10397103475940294514559553)
        ·
          refine ⟨7797827606955220885919665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10397103475940294514559553 7797827606955220885919665)
          ·
            refine ⟨5848370705216415664439749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7797827606955220885919665 5848370705216415664439749)
            ·
              refine ⟨1096569507228077937082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5848370705216415664439749 1096569507228077937082453)
              ·
                refine ⟨12850423912829038325185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1096569507228077937082453 12850423912829038325185)
                ·
                  rfl

theorem cell23_675705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 8].length) (baseStart_675705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675705 prefixEnd_675705 := by exact prefixLift 675705
  have htrace : WordTrace (prefixWord ++ tailWord_675705) baseStart_675705 baseEnd_675705 := by
    simpa [prefixWord, tailWord_675705, baseEnd_675705] using wordTrace_append hprefix tailTrace_675705
  have hstable : (prefixWord ++ tailWord_675705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675705).length < 2 ^ (prefixWord ++ tailWord_675705).sum := by decide
  have hdescent : baseEnd_675705 < baseStart_675705 := by decide
  rcases family_descends (prefixWord ++ tailWord_675705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675713 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_675713 : Nat := 118140960795 + 675713 * 2 ^ 59
def prefixEnd_675713 : Nat := 4983230072969 + 3 ^ 40 * 675713 * 2
def baseEnd_675713 : Nat := 115655184497206667826653

theorem tailTrace_675713 : CollatzResearch.WordTrace tailWord_675713 prefixEnd_675713 115655184497206667826653 := by
  unfold tailWord_675713
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645277801014678437839793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16430185200676452291893195 24645277801014678437839793)
  ·
    refine ⟨18483958350761008828379845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24645277801014678437839793 18483958350761008828379845)
    ·
      refine ⟨3465742190767689155321221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18483958350761008828379845 3465742190767689155321221)
      ·
        refine ⟨649826660768941716622729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3465742190767689155321221 649826660768941716622729)
        ·
          refine ⟨487369995576706287467047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 649826660768941716622729 487369995576706287467047)
          ·
            refine ⟨731054993365059431200571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487369995576706287467047 731054993365059431200571)
            ·
              refine ⟨1096582490047589146800857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731054993365059431200571 1096582490047589146800857)
              ·
                refine ⟨822436867535691860100643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096582490047589146800857 822436867535691860100643)
                ·
                  refine ⟨1233655301303537790150965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822436867535691860100643 1233655301303537790150965)
                  ·
                    refine ⟨115655184497206667826653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1233655301303537790150965 115655184497206667826653)
                    ·
                      rfl

theorem cell23_675713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_675713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675713 prefixEnd_675713 := by exact prefixLift 675713
  have htrace : WordTrace (prefixWord ++ tailWord_675713) baseStart_675713 baseEnd_675713 := by
    simpa [prefixWord, tailWord_675713, baseEnd_675713] using wordTrace_append hprefix tailTrace_675713
  have hstable : (prefixWord ++ tailWord_675713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675713).length < 2 ^ (prefixWord ++ tailWord_675713).sum := by decide
  have hdescent : baseEnd_675713 < baseStart_675713 := by decide
  rcases family_descends (prefixWord ++ tailWord_675713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675719 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_675719 : Nat := 118140960795 + 675719 * 2 ^ 59
def prefixEnd_675719 : Nat := 4983230072969 + 3 ^ 40 * 675719 * 2
def baseEnd_675719 : Nat := 346968634375546980004931

theorem tailTrace_675719 : CollatzResearch.WordTrace tailWord_675719 prefixEnd_675719 346968634375546980004931 := by
  unfold tailWord_675719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645496638992941462558211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16430331092661960975038807 24645496638992941462558211)
  ·
    refine ⟨36968244958489412193837317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24645496638992941462558211 36968244958489412193837317)
    ·
      refine ⟨6931545929716764786344497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36968244958489412193837317 6931545929716764786344497)
      ·
        refine ⟨5198659447287573589758373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6931545929716764786344497 5198659447287573589758373)
        ·
          refine ⟨974748646366420048079695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5198659447287573589758373 974748646366420048079695)
          ·
            refine ⟨1462122969549630072119543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974748646366420048079695 1462122969549630072119543)
            ·
              refine ⟨2193184454324445108179315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462122969549630072119543 2193184454324445108179315)
              ·
                refine ⟨3289776681486667662268973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193184454324445108179315 3289776681486667662268973)
                ·
                  refine ⟨1233666255557500373350865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3289776681486667662268973 1233666255557500373350865)
                  ·
                    refine ⟨925249691668125280013149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233666255557500373350865 925249691668125280013149)
                    ·
                      refine ⟨346968634375546980004931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 925249691668125280013149 346968634375546980004931)
                      ·
                        rfl

theorem cell23_675719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_675719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675719 prefixEnd_675719 := by exact prefixLift 675719
  have htrace : WordTrace (prefixWord ++ tailWord_675719) baseStart_675719 baseEnd_675719 := by
    simpa [prefixWord, tailWord_675719, baseEnd_675719] using wordTrace_append hprefix tailTrace_675719
  have hstable : (prefixWord ++ tailWord_675719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675719).length < 2 ^ (prefixWord ++ tailWord_675719).sum := by decide
  have hdescent : baseEnd_675719 < baseStart_675719 := by decide
  rcases family_descends (prefixWord ++ tailWord_675719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675736 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_675736 : Nat := 118140960795 + 675736 * 2 ^ 59
def prefixEnd_675736 : Nat := 4983230072969 + 3 ^ 40 * 675736 * 2
def baseEnd_675736 : Nat := 346977363546673413492353

theorem tailTrace_675736 : CollatzResearch.WordTrace tailWord_675736 prefixEnd_675736 346977363546673413492353 := by
  unfold tailWord_675736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323058339965676682963531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16430744453287568910618041 12323058339965676682963531)
  ·
    refine ⟨18484587509948515024445297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323058339965676682963531 18484587509948515024445297)
    ·
      refine ⟨13863440632461386268333973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18484587509948515024445297 13863440632461386268333973)
      ·
        refine ⟨649848779646627481328155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13863440632461386268333973 649848779646627481328155)
        ·
          refine ⟨974773169469941221992233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 649848779646627481328155 974773169469941221992233)
          ·
            refine ⟨731079877102455916494175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974773169469941221992233 731079877102455916494175)
            ·
              refine ⟨1096619815653683874741263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731079877102455916494175 1096619815653683874741263)
              ·
                refine ⟨1644929723480525812111895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096619815653683874741263 1644929723480525812111895)
                ·
                  refine ⟨2467394585220788718167843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644929723480525812111895 2467394585220788718167843)
                  ·
                    refine ⟨3701091877831183077251765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467394585220788718167843 3701091877831183077251765)
                    ·
                      refine ⟨346977363546673413492353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3701091877831183077251765 346977363546673413492353)
                      ·
                        rfl

theorem cell23_675736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_675736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675736 prefixEnd_675736 := by exact prefixLift 675736
  have htrace : WordTrace (prefixWord ++ tailWord_675736) baseStart_675736 baseEnd_675736 := by
    simpa [prefixWord, tailWord_675736, baseEnd_675736] using wordTrace_append hprefix tailTrace_675736
  have hstable : (prefixWord ++ tailWord_675736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675736).length < 2 ^ (prefixWord ++ tailWord_675736).sum := by decide
  have hdescent : baseEnd_675736 < baseStart_675736 := by decide
  rcases family_descends (prefixWord ++ tailWord_675736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675812 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 7]
def baseStart_675812 : Nat := 118140960795 + 675812 * 2 ^ 59
def prefixEnd_675812 : Nat := 4983230072969 + 3 ^ 40 * 675812 * 2
def baseEnd_675812 : Nat := 38557376452935012904667

theorem tailTrace_675812 : CollatzResearch.WordTrace tailWord_675812 prefixEnd_675812 38557376452935012904667 := by
  unfold tailWord_675812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324444313828009172846845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16432592418437345563795793 12324444313828009172846845)
  ·
    refine ⟨4621666617685503439817567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12324444313828009172846845 4621666617685503439817567)
    ·
      refine ⟨6932499926528255159726351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621666617685503439817567 6932499926528255159726351)
      ·
        refine ⟨10398749889792382739589527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6932499926528255159726351 10398749889792382739589527)
        ·
          refine ⟨15598124834688574109384291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398749889792382739589527 15598124834688574109384291)
          ·
            refine ⟨23397187252032861164076437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15598124834688574109384291 23397187252032861164076437)
            ·
              refine ⟨1096743152439040367066083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23397187252032861164076437 1096743152439040367066083)
              ·
                refine ⟨1645114728658560550599125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096743152439040367066083 1645114728658560550599125)
                ·
                  refine ⟨38557376452935012904667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1645114728658560550599125 38557376452935012904667)
                  ·
                    rfl

theorem cell23_675812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_675812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675812 prefixEnd_675812 := by exact prefixLift 675812
  have htrace : WordTrace (prefixWord ++ tailWord_675812) baseStart_675812 baseEnd_675812 := by
    simpa [prefixWord, tailWord_675812, baseEnd_675812] using wordTrace_append hprefix tailTrace_675812
  have hstable : (prefixWord ++ tailWord_675812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675812).length < 2 ^ (prefixWord ++ tailWord_675812).sum := by decide
  have hdescent : baseEnd_675812 < baseStart_675812 := by decide
  rcases family_descends (prefixWord ++ tailWord_675812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675823 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 2, 2, 2]
def baseStart_675823 : Nat := 118140960795 + 675823 * 2 ^ 59
def prefixEnd_675823 : Nat := 4983230072969 + 3 ^ 40 * 675823 * 2
def baseEnd_675823 : Nat := 347022036363614573104453

theorem tailTrace_675823 : CollatzResearch.WordTrace tailWord_675823 prefixEnd_675823 347022036363614573104453 := by
  unfold tailWord_675823
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649289830616167224344123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16432859887077444816229415 24649289830616167224344123)
  ·
    refine ⟨36973934745924250836516185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24649289830616167224344123 36973934745924250836516185)
    ·
      refine ⟨27730451059443188127387139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36973934745924250836516185 27730451059443188127387139)
      ·
        refine ⟨41595676589164782191080709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27730451059443188127387139 41595676589164782191080709)
        ·
          refine ⟨7799189360468396660827633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41595676589164782191080709 7799189360468396660827633)
          ·
            refine ⟨5849392020351297495620725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7799189360468396660827633 5849392020351297495620725)
            ·
              refine ⟨548380501907934140214443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5849392020351297495620725 548380501907934140214443)
              ·
                refine ⟨822570752861901210321665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548380501907934140214443 822570752861901210321665)
                ·
                  refine ⟨616928064646425907741249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822570752861901210321665 616928064646425907741249)
                  ·
                    refine ⟨462696048484819430805937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616928064646425907741249 462696048484819430805937)
                    ·
                      refine ⟨347022036363614573104453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462696048484819430805937 347022036363614573104453)
                      ·
                        rfl

theorem cell23_675823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 2, 2, 2].length) (baseStart_675823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675823 prefixEnd_675823 := by exact prefixLift 675823
  have htrace : WordTrace (prefixWord ++ tailWord_675823) baseStart_675823 baseEnd_675823 := by
    simpa [prefixWord, tailWord_675823, baseEnd_675823] using wordTrace_append hprefix tailTrace_675823
  have hstable : (prefixWord ++ tailWord_675823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675823).length < 2 ^ (prefixWord ++ tailWord_675823).sum := by decide
  have hdescent : baseEnd_675823 < baseStart_675823 := by decide
  rcases family_descends (prefixWord ++ tailWord_675823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675852 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_675852 : Nat := 118140960795 + 675852 * 2 ^ 59
def prefixEnd_675852 : Nat := 4983230072969 + 3 ^ 40 * 675852 * 2
def baseEnd_675852 : Nat := 347036927302594959641819

theorem tailTrace_675852 : CollatzResearch.WordTrace tailWord_675852 prefixEnd_675852 347036927302594959641819 := by
  unfold tailWord_675852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325173773755552588574905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16433565031674070118099873 12325173773755552588574905)
  ·
    refine ⟨9243880330316664441431179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12325173773755552588574905 9243880330316664441431179)
    ·
      refine ⟨13865820495474996662146769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243880330316664441431179 13865820495474996662146769)
      ·
        refine ⟨10399365371606247496610077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13865820495474996662146769 10399365371606247496610077)
        ·
          refine ⟨3899762014352342811228779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10399365371606247496610077 3899762014352342811228779)
          ·
            refine ⟨5849643021528514216843169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899762014352342811228779 5849643021528514216843169)
            ·
              refine ⟨4387232266146385662632377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849643021528514216843169 4387232266146385662632377)
              ·
                refine ⟨3290424199609789246974283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4387232266146385662632377 3290424199609789246974283)
                ·
                  refine ⟨4935636299414683870461425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290424199609789246974283 4935636299414683870461425)
                  ·
                    refine ⟨3701727224561012902846069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935636299414683870461425 3701727224561012902846069)
                    ·
                      refine ⟨347036927302594959641819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3701727224561012902846069 347036927302594959641819)
                      ·
                        rfl

theorem cell23_675852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_675852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675852 prefixEnd_675852 := by exact prefixLift 675852
  have htrace : WordTrace (prefixWord ++ tailWord_675852) baseStart_675852 baseEnd_675852 := by
    simpa [prefixWord, tailWord_675852, baseEnd_675852] using wordTrace_append hprefix tailTrace_675852
  have hstable : (prefixWord ++ tailWord_675852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675852).length < 2 ^ (prefixWord ++ tailWord_675852).sum := by decide
  have hdescent : baseEnd_675852 < baseStart_675852 := by decide
  rcases family_descends (prefixWord ++ tailWord_675852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675863 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 5]
def baseStart_675863 : Nat := 118140960795 + 675863 * 2 ^ 59
def prefixEnd_675863 : Nat := 4983230072969 + 3 ^ 40 * 675863 * 2
def baseEnd_675863 : Nat := 38560286176643824067141

theorem tailTrace_675863 : CollatzResearch.WordTrace tailWord_675863 prefixEnd_675863 38560286176643824067141 := by
  unfold tailWord_675863
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650748750471254055800243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16433832500314169370533495 24650748750471254055800243)
  ·
    refine ⟨36976123125706881083700365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650748750471254055800243 36976123125706881083700365)
    ·
      refine ⟨13866046172140080406387637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36976123125706881083700365 13866046172140080406387637)
      ·
        refine ⟨1299941828638132538098841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13866046172140080406387637 1299941828638132538098841)
        ·
          refine ⟨974956371478599403574131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299941828638132538098841 974956371478599403574131)
          ·
            refine ⟨1462434557217899105361197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974956371478599403574131 1462434557217899105361197)
            ·
              refine ⟨548412958956712164510449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1462434557217899105361197 548412958956712164510449)
              ·
                refine ⟨411309719217534123382837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548412958956712164510449 411309719217534123382837)
                ·
                  refine ⟨38560286176643824067141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411309719217534123382837 38560286176643824067141)
                  ·
                    rfl

theorem cell23_675863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 5].length) (baseStart_675863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675863 prefixEnd_675863 := by exact prefixLift 675863
  have htrace : WordTrace (prefixWord ++ tailWord_675863) baseStart_675863 baseEnd_675863 := by
    simpa [prefixWord, tailWord_675863, baseEnd_675863] using wordTrace_append hprefix tailTrace_675863
  have hstable : (prefixWord ++ tailWord_675863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675863).length < 2 ^ (prefixWord ++ tailWord_675863).sum := by decide
  have hdescent : baseEnd_675863 < baseStart_675863 := by decide
  rcases family_descends (prefixWord ++ tailWord_675863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675869 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_675869 : Nat := 118140960795 + 675869 * 2 ^ 59
def prefixEnd_675869 : Nat := 4983230072969 + 3 ^ 40 * 675869 * 2
def baseEnd_675869 : Nat := 347045656473721393129241

theorem tailTrace_675869 : CollatzResearch.WordTrace tailWord_675869 prefixEnd_675869 347045656473721393129241 := by
  unfold tailWord_675869
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650967588449517080518661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16433978392299678053679107 24650967588449517080518661)
  ·
    refine ⟨4622056422834284452597249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24650967588449517080518661 4622056422834284452597249)
    ·
      refine ⟨3466542317125713339447937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4622056422834284452597249 3466542317125713339447937)
      ·
        refine ⟨2599906737844285004585953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3466542317125713339447937 2599906737844285004585953)
        ·
          refine ⟨1949930053383213753439465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599906737844285004585953 1949930053383213753439465)
          ·
            refine ⟨1462447540037410315079599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949930053383213753439465 1462447540037410315079599)
            ·
              refine ⟨2193671310056115472619399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462447540037410315079599 2193671310056115472619399)
              ·
                refine ⟨3290506965084173208929099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193671310056115472619399 3290506965084173208929099)
                ·
                  refine ⟨4935760447626259813393649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290506965084173208929099 4935760447626259813393649)
                  ·
                    refine ⟨3701820335719694860045237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935760447626259813393649 3701820335719694860045237)
                    ·
                      refine ⟨347045656473721393129241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3701820335719694860045237 347045656473721393129241)
                      ·
                        rfl

theorem cell23_675869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_675869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675869 prefixEnd_675869 := by exact prefixLift 675869
  have htrace : WordTrace (prefixWord ++ tailWord_675869) baseStart_675869 baseEnd_675869 := by
    simpa [prefixWord, tailWord_675869, baseEnd_675869] using wordTrace_append hprefix tailTrace_675869
  have hstable : (prefixWord ++ tailWord_675869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675869).length < 2 ^ (prefixWord ++ tailWord_675869).sum := by decide
  have hdescent : baseEnd_675869 < baseStart_675869 := by decide
  rcases family_descends (prefixWord ++ tailWord_675869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675896 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_675896 : Nat := 118140960795 + 675896 * 2 ^ 59
def prefixEnd_675896 : Nat := 4983230072969 + 3 ^ 40 * 675896 * 2
def baseEnd_675896 : Nat := 347059520451392787491617

theorem tailTrace_675896 : CollatzResearch.WordTrace tailWord_675896 prefixEnd_675896 347059520451392787491617 := by
  unfold tailWord_675896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325976179675850345875771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16434634906234467127834361 12325976179675850345875771)
  ·
    refine ⟨18488964269513775518813657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12325976179675850345875771 18488964269513775518813657)
    ·
      refine ⟨13866723202135331639110243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18488964269513775518813657 13866723202135331639110243)
      ·
        refine ⟨20800084803202997458665365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13866723202135331639110243 20800084803202997458665365)
        ·
          refine ⟨975003975150140505874939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20800084803202997458665365 975003975150140505874939)
          ·
            refine ⟨1462505962725210758812409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975003975150140505874939 1462505962725210758812409)
            ·
              refine ⟨1096879472043908069109307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462505962725210758812409 1096879472043908069109307)
              ·
                refine ⟨1645319208065862103663961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096879472043908069109307 1645319208065862103663961)
                ·
                  refine ⟨1233989406049396577747971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645319208065862103663961 1233989406049396577747971)
                  ·
                    refine ⟨1850984109074094866621957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233989406049396577747971 1850984109074094866621957)
                    ·
                      refine ⟨347059520451392787491617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1850984109074094866621957 347059520451392787491617)
                      ·
                        rfl

theorem cell23_675896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_675896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675896 prefixEnd_675896 := by exact prefixLift 675896
  have htrace : WordTrace (prefixWord ++ tailWord_675896) baseStart_675896 baseEnd_675896 := by
    simpa [prefixWord, tailWord_675896, baseEnd_675896] using wordTrace_append hprefix tailTrace_675896
  have hstable : (prefixWord ++ tailWord_675896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675896).length < 2 ^ (prefixWord ++ tailWord_675896).sum := by decide
  have hdescent : baseEnd_675896 < baseStart_675896 := by decide
  rcases family_descends (prefixWord ++ tailWord_675896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675949 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_675949 : Nat := 118140960795 + 675949 * 2 ^ 59
def prefixEnd_675949 : Nat := 4983230072969 + 3 ^ 40 * 675949 * 2
def baseEnd_675949 : Nat := 115695578308693693376291

theorem tailTrace_675949 : CollatzResearch.WordTrace tailWord_675949 prefixEnd_675949 115695578308693693376291 := by
  unfold tailWord_675949
  simp only [CollatzResearch.WordTrace]
  refine ⟨24653885428159690743430901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16435923618773127162287267 24653885428159690743430901)
  ·
    refine ⟨2311301758889971007196647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24653885428159690743430901 2311301758889971007196647)
    ·
      refine ⟨3466952638334956510794971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311301758889971007196647 3466952638334956510794971)
      ·
        refine ⟨5200428957502434766192457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466952638334956510794971 5200428957502434766192457)
        ·
          refine ⟨3900321718126826074644343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5200428957502434766192457 3900321718126826074644343)
          ·
            refine ⟨5850482577190239111966515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900321718126826074644343 5850482577190239111966515)
            ·
              refine ⟨8775723865785358667949773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850482577190239111966515 8775723865785358667949773)
              ·
                refine ⟨3290896449669509500481165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8775723865785358667949773 3290896449669509500481165)
                ·
                  refine ⟨1234086168626066062680437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3290896449669509500481165 1234086168626066062680437)
                  ·
                    refine ⟨115695578308693693376291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1234086168626066062680437 115695578308693693376291)
                    ·
                      rfl

theorem cell23_675949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_675949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675949 prefixEnd_675949 := by exact prefixLift 675949
  have htrace : WordTrace (prefixWord ++ tailWord_675949) baseStart_675949 baseEnd_675949 := by
    simpa [prefixWord, tailWord_675949, baseEnd_675949] using wordTrace_append hprefix tailTrace_675949
  have hstable : (prefixWord ++ tailWord_675949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675949).length < 2 ^ (prefixWord ++ tailWord_675949).sum := by decide
  have hdescent : baseEnd_675949 < baseStart_675949 := by decide
  rcases family_descends (prefixWord ++ tailWord_675949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_675989 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_675989 : Nat := 118140960795 + 675989 * 2 ^ 59
def prefixEnd_675989 : Nat := 4983230072969 + 3 ^ 40 * 675989 * 2
def baseEnd_675989 : Nat := 347107274152260923628689

theorem tailTrace_675989 : CollatzResearch.WordTrace tailWord_675989 prefixEnd_675989 347107274152260923628689 := by
  unfold tailWord_675989
  simp only [CollatzResearch.WordTrace]
  refine ⟨24655344348014777574887021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16436896232009851716591347 24655344348014777574887021)
  ·
    refine ⟨9245754130505541590582633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24655344348014777574887021 9245754130505541590582633)
    ·
      refine ⟨6934315597879156192936975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9245754130505541590582633 6934315597879156192936975)
      ·
        refine ⟨10401473396818734289405463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934315597879156192936975 10401473396818734289405463)
        ·
          refine ⟨15602210095228101434108195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10401473396818734289405463 15602210095228101434108195)
          ·
            refine ⟨23403315142842152151162293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15602210095228101434108195 23403315142842152151162293)
            ·
              refine ⟨2194060794641451764171465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23403315142842152151162293 2194060794641451764171465)
              ·
                refine ⟨1645545595981088823128599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194060794641451764171465 1645545595981088823128599)
                ·
                  refine ⟨2468318393971633234692899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645545595981088823128599 2468318393971633234692899)
                  ·
                    refine ⟨3702477590957449852039349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2468318393971633234692899 3702477590957449852039349)
                    ·
                      refine ⟨347107274152260923628689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3702477590957449852039349 347107274152260923628689)
                      ·
                        rfl

theorem cell23_675989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_675989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_675989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_675989 prefixEnd_675989 := by exact prefixLift 675989
  have htrace : WordTrace (prefixWord ++ tailWord_675989) baseStart_675989 baseEnd_675989 := by
    simpa [prefixWord, tailWord_675989, baseEnd_675989] using wordTrace_append hprefix tailTrace_675989
  have hstable : (prefixWord ++ tailWord_675989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_675989).length < 2 ^ (prefixWord ++ tailWord_675989).sum := by decide
  have hdescent : baseEnd_675989 < baseStart_675989 := by decide
  rcases family_descends (prefixWord ++ tailWord_675989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676019 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3]
def baseStart_676019 : Nat := 118140960795 + 676019 * 2 ^ 59
def prefixEnd_676019 : Nat := 4983230072969 + 3 ^ 40 * 676019 * 2
def baseEnd_676019 : Nat := 347122678571895806253551

theorem tailTrace_676019 : CollatzResearch.WordTrace tailWord_676019 prefixEnd_676019 347122678571895806253551 := by
  unfold tailWord_676019
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656438537906092698479111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16437625691937395132319407 24656438537906092698479111)
  ·
    refine ⟨36984657806859139047718667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24656438537906092698479111 36984657806859139047718667)
    ·
      refine ⟨55476986710288708571578001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36984657806859139047718667 55476986710288708571578001)
      ·
        refine ⟨41607740032716531428683501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55476986710288708571578001 41607740032716531428683501)
        ·
          refine ⟨15602902512268699285756313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41607740032716531428683501 15602902512268699285756313)
          ·
            refine ⟨11702176884201524464317235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15602902512268699285756313 11702176884201524464317235)
            ·
              refine ⟨17553265326302286696475853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11702176884201524464317235 17553265326302286696475853)
              ·
                refine ⟨6582474497363357511178445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17553265326302286696475853 6582474497363357511178445)
                ·
                  refine ⟨2468427936511259066691917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6582474497363357511178445 2468427936511259066691917)
                  ·
                    refine ⟨925660476191722150009469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468427936511259066691917 925660476191722150009469)
                    ·
                      refine ⟨347122678571895806253551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 925660476191722150009469 347122678571895806253551)
                      ·
                        rfl

theorem cell23_676019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_676019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676019 prefixEnd_676019 := by exact prefixLift 676019
  have htrace : WordTrace (prefixWord ++ tailWord_676019) baseStart_676019 baseEnd_676019 := by
    simpa [prefixWord, tailWord_676019, baseEnd_676019] using wordTrace_append hprefix tailTrace_676019
  have hstable : (prefixWord ++ tailWord_676019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676019).length < 2 ^ (prefixWord ++ tailWord_676019).sum := by decide
  have hdescent : baseEnd_676019 < baseStart_676019 := by decide
  rcases family_descends (prefixWord ++ tailWord_676019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676093 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_676093 : Nat := 118140960795 + 676093 * 2 ^ 59
def prefixEnd_676093 : Nat := 4983230072969 + 3 ^ 40 * 676093 * 2
def baseEnd_676093 : Nat := 347160676140328516728211

theorem tailTrace_676093 : CollatzResearch.WordTrace tailWord_676093 prefixEnd_676093 347160676140328516728211 := by
  unfold tailWord_676093
  simp only [CollatzResearch.WordTrace]
  refine ⟨24659137539638003336672933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16439425026425335557781955 24659137539638003336672933)
  ·
    refine ⟨4623588288682125625626175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24659137539638003336672933 4623588288682125625626175)
    ·
      refine ⟨6935382433023188438439263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623588288682125625626175 6935382433023188438439263)
      ·
        refine ⟨10403073649534782657658895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935382433023188438439263 10403073649534782657658895)
        ·
          refine ⟨15604610474302173986488343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10403073649534782657658895 15604610474302173986488343)
          ·
            refine ⟨23406915711453260979732515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15604610474302173986488343 23406915711453260979732515)
            ·
              refine ⟨35110373567179891469598773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23406915711453260979732515 35110373567179891469598773)
              ·
                refine ⟨3291597521923114825274885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35110373567179891469598773 3291597521923114825274885)
                ·
                  refine ⟨617174535360584029739041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3291597521923114825274885 617174535360584029739041)
                  ·
                    refine ⟨462880901520438022304281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617174535360584029739041 462880901520438022304281)
                    ·
                      refine ⟨347160676140328516728211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462880901520438022304281 347160676140328516728211)
                      ·
                        rfl

theorem cell23_676093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_676093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676093 prefixEnd_676093 := by exact prefixLift 676093
  have htrace : WordTrace (prefixWord ++ tailWord_676093) baseStart_676093 baseEnd_676093 := by
    simpa [prefixWord, tailWord_676093, baseEnd_676093] using wordTrace_append hprefix tailTrace_676093
  have hstable : (prefixWord ++ tailWord_676093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676093).length < 2 ^ (prefixWord ++ tailWord_676093).sum := by decide
  have hdescent : baseEnd_676093 < baseStart_676093 := by decide
  rcases family_descends (prefixWord ++ tailWord_676093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676099 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 7]
def baseStart_676099 : Nat := 118140960795 + 676099 * 2 ^ 59
def prefixEnd_676099 : Nat := 4983230072969 + 3 ^ 40 * 676099 * 2
def baseEnd_676099 : Nat := 38573750780472832583687

theorem tailTrace_676099 : CollatzResearch.WordTrace tailWord_676099 prefixEnd_676099 38573750780472832583687 := by
  unfold tailWord_676099
  simp only [CollatzResearch.WordTrace]
  refine ⟨24659356377616266361391351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16439570918410844240927567 24659356377616266361391351)
  ·
    refine ⟨36989034566424399542087027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24659356377616266361391351 36989034566424399542087027)
    ·
      refine ⟨55483551849636599313130541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36989034566424399542087027 55483551849636599313130541)
      ·
        refine ⟨20806331943613724742423953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55483551849636599313130541 20806331943613724742423953)
        ·
          refine ⟨15604748957710293556817965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20806331943613724742423953 15604748957710293556817965)
          ·
            refine ⟨5851780859141360083806737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15604748957710293556817965 5851780859141360083806737)
            ·
              refine ⟨4388835644356020062855053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851780859141360083806737 4388835644356020062855053)
              ·
                refine ⟨1645813366633507523570645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4388835644356020062855053 1645813366633507523570645)
                ·
                  refine ⟨38573750780472832583687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1645813366633507523570645 38573750780472832583687)
                  ·
                    rfl

theorem cell23_676099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 7].length) (baseStart_676099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676099 prefixEnd_676099 := by exact prefixLift 676099
  have htrace : WordTrace (prefixWord ++ tailWord_676099) baseStart_676099 baseEnd_676099 := by
    simpa [prefixWord, tailWord_676099, baseEnd_676099] using wordTrace_append hprefix tailTrace_676099
  have hstable : (prefixWord ++ tailWord_676099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676099).length < 2 ^ (prefixWord ++ tailWord_676099).sum := by decide
  have hdescent : baseEnd_676099 < baseStart_676099 := by decide
  rcases family_descends (prefixWord ++ tailWord_676099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676103 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 6]
def baseStart_676103 : Nat := 118140960795 + 676103 * 2 ^ 59
def prefixEnd_676103 : Nat := 4983230072969 + 3 ^ 40 * 676103 * 2
def baseEnd_676103 : Nat := 115721936982291159201055

theorem tailTrace_676103 : CollatzResearch.WordTrace tailWord_676103 prefixEnd_676103 115721936982291159201055 := by
  unfold tailWord_676103
  simp only [CollatzResearch.WordTrace]
  refine ⟨24659502269601775044536963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16439668179734516696357975 24659502269601775044536963)
  ·
    refine ⟨36989253404402662566805445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24659502269601775044536963 36989253404402662566805445)
    ·
      refine ⟨6935485013325499231276021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36989253404402662566805445 6935485013325499231276021)
      ·
        refine ⟨650201719999265552932127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6935485013325499231276021 650201719999265552932127)
        ·
          refine ⟨975302579998898329398191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650201719999265552932127 975302579998898329398191)
          ·
            refine ⟨1462953869998347494097287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975302579998898329398191 1462953869998347494097287)
            ·
              refine ⟨2194430804997521241145931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462953869998347494097287 2194430804997521241145931)
              ·
                refine ⟨3291646207496281861718897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194430804997521241145931 3291646207496281861718897)
                ·
                  refine ⟨2468734655622211396289173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291646207496281861718897 2468734655622211396289173)
                  ·
                    refine ⟨115721936982291159201055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2468734655622211396289173 115721936982291159201055)
                    ·
                      rfl

theorem cell23_676103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_676103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676103 prefixEnd_676103 := by exact prefixLift 676103
  have htrace : WordTrace (prefixWord ++ tailWord_676103) baseStart_676103 baseEnd_676103 := by
    simpa [prefixWord, tailWord_676103, baseEnd_676103] using wordTrace_append hprefix tailTrace_676103
  have hstable : (prefixWord ++ tailWord_676103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676103).length < 2 ^ (prefixWord ++ tailWord_676103).sum := by decide
  have hdescent : baseEnd_676103 < baseStart_676103 := by decide
  rcases family_descends (prefixWord ++ tailWord_676103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676110 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_676110 : Nat := 118140960795 + 676110 * 2 ^ 59
def prefixEnd_676110 : Nat := 4983230072969 + 3 ^ 40 * 676110 * 2
def baseEnd_676110 : Nat := 347169405311454950215633

theorem tailTrace_676110 : CollatzResearch.WordTrace tailWord_676110 prefixEnd_676110 347169405311454950215633 := by
  unfold tailWord_676110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082469697572051905005223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16439838387050943493361189 3082469697572051905005223)
  ·
    refine ⟨4623704546358077857507835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082469697572051905005223 4623704546358077857507835)
    ·
      refine ⟨6935556819537116786261753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623704546358077857507835 6935556819537116786261753)
      ·
        refine ⟨5201667614652837589696315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6935556819537116786261753 5201667614652837589696315)
        ·
          refine ⟨7802501421979256384544473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201667614652837589696315 7802501421979256384544473)
          ·
            refine ⟨5851876066484442288408355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802501421979256384544473 5851876066484442288408355)
            ·
              refine ⟨8777814099726663432612533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851876066484442288408355 8777814099726663432612533)
              ·
                refine ⟨822920071849374696807425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8777814099726663432612533 822920071849374696807425)
                ·
                  refine ⟨617190053887031022605569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822920071849374696807425 617190053887031022605569)
                  ·
                    refine ⟨462892540415273266954177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617190053887031022605569 462892540415273266954177)
                    ·
                      refine ⟨347169405311454950215633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462892540415273266954177 347169405311454950215633)
                      ·
                        rfl

theorem cell23_676110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_676110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676110 prefixEnd_676110 := by exact prefixLift 676110
  have htrace : WordTrace (prefixWord ++ tailWord_676110) baseStart_676110 baseEnd_676110 := by
    simpa [prefixWord, tailWord_676110, baseEnd_676110] using wordTrace_append hprefix tailTrace_676110
  have hstable : (prefixWord ++ tailWord_676110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676110).length < 2 ^ (prefixWord ++ tailWord_676110).sum := by decide
  have hdescent : baseEnd_676110 < baseStart_676110 := by decide
  rcases family_descends (prefixWord ++ tailWord_676110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676179 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_676179 : Nat := 118140960795 + 676179 * 2 ^ 59
def prefixEnd_676179 : Nat := 4983230072969 + 3 ^ 40 * 676179 * 2
def baseEnd_676179 : Nat := 347204835476615180252815

theorem tailTrace_676179 : CollatzResearch.WordTrace tailWord_676179 prefixEnd_676179 347204835476615180252815 := by
  unfold tailWord_676179
  simp only [CollatzResearch.WordTrace]
  refine ⟨24662274217326440024303591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16441516144884293349535727 24662274217326440024303591)
  ·
    refine ⟨36993411325989660036455387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24662274217326440024303591 36993411325989660036455387)
    ·
      refine ⟨55490116988984490054683081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36993411325989660036455387 55490116988984490054683081)
      ·
        refine ⟨41617587741738367541012311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55490116988984490054683081 41617587741738367541012311)
        ·
          refine ⟨62426381612607551311518467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41617587741738367541012311 62426381612607551311518467)
          ·
            refine ⟨93639572418911326967277701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62426381612607551311518467 93639572418911326967277701)
            ·
              refine ⟨17557419828545873806364569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93639572418911326967277701 17557419828545873806364569)
              ·
                refine ⟨13168064871409405354773427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17557419828545873806364569 13168064871409405354773427)
                ·
                  refine ⟨19752097307114108032160141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13168064871409405354773427 19752097307114108032160141)
                  ·
                    refine ⟨7407036490167790512060053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19752097307114108032160141 7407036490167790512060053)
                    ·
                      refine ⟨347204835476615180252815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7407036490167790512060053 347204835476615180252815)
                      ·
                        rfl

theorem cell23_676179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_676179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676179 prefixEnd_676179 := by exact prefixLift 676179
  have htrace : WordTrace (prefixWord ++ tailWord_676179) baseStart_676179 baseEnd_676179 := by
    simpa [prefixWord, tailWord_676179, baseEnd_676179] using wordTrace_append hprefix tailTrace_676179
  have hstable : (prefixWord ++ tailWord_676179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676179).length < 2 ^ (prefixWord ++ tailWord_676179).sum := by decide
  have hdescent : baseEnd_676179 < baseStart_676179 := by decide
  rcases family_descends (prefixWord ++ tailWord_676179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676210 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_676210 : Nat := 118140960795 + 676210 * 2 ^ 59
def prefixEnd_676210 : Nat := 4983230072969 + 3 ^ 40 * 676210 * 2
def baseEnd_676210 : Nat := 115740251125634852988391

theorem tailTrace_676210 : CollatzResearch.WordTrace tailWord_676210 prefixEnd_676210 115740251125634852988391 := by
  unfold tailWord_676210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165851220053533079670521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16442269920142754879121389 6165851220053533079670521)
  ·
    refine ⟨4624388415040149809752891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6165851220053533079670521 4624388415040149809752891)
    ·
      refine ⟨6936582622560224714629337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624388415040149809752891 6936582622560224714629337)
      ·
        refine ⟨5202436966920168535972003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6936582622560224714629337 5202436966920168535972003)
        ·
          refine ⟨7803655450380252803958005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202436966920168535972003 7803655450380252803958005)
          ·
            refine ⟨731592698473148700371063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7803655450380252803958005 731592698473148700371063)
            ·
              refine ⟨1097389047709723050556595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731592698473148700371063 1097389047709723050556595)
              ·
                refine ⟨1646083571564584575834893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097389047709723050556595 1646083571564584575834893)
                ·
                  refine ⟨617281339336719215938085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1646083571564584575834893 617281339336719215938085)
                  ·
                    refine ⟨115740251125634852988391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617281339336719215938085 115740251125634852988391)
                    ·
                      rfl

theorem cell23_676210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_676210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676210 prefixEnd_676210 := by exact prefixLift 676210
  have htrace : WordTrace (prefixWord ++ tailWord_676210) baseStart_676210 baseEnd_676210 := by
    simpa [prefixWord, tailWord_676210, baseEnd_676210] using wordTrace_append hprefix tailTrace_676210
  have hstable : (prefixWord ++ tailWord_676210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676210).length < 2 ^ (prefixWord ++ tailWord_676210).sum := by decide
  have hdescent : baseEnd_676210 < baseStart_676210 := by decide
  rcases family_descends (prefixWord ++ tailWord_676210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676260 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_676260 : Nat := 118140960795 + 676260 * 2 ^ 59
def prefixEnd_676260 : Nat := 4983230072969 + 3 ^ 40 * 676260 * 2
def baseEnd_676260 : Nat := 347246427409629363339943

theorem tailTrace_676260 : CollatzResearch.WordTrace tailWord_676260 prefixEnd_676260 347246427409629363339943 := by
  unfold tailWord_676260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332614265016495429001117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16443485686688660572001489 12332614265016495429001117)
  ·
    refine ⟨4624730349381185785875419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12332614265016495429001117 4624730349381185785875419)
    ·
      refine ⟨6937095524071778678813129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624730349381185785875419 6937095524071778678813129)
      ·
        refine ⟨5202821643053834009109847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6937095524071778678813129 5202821643053834009109847)
        ·
          refine ⟨7804232464580751013664771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202821643053834009109847 7804232464580751013664771)
          ·
            refine ⟨11706348696871126520497157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7804232464580751013664771 11706348696871126520497157)
            ·
              refine ⟨2194940380663336222593217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11706348696871126520497157 2194940380663336222593217)
              ·
                refine ⟨1646205285497502166944913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194940380663336222593217 1646205285497502166944913)
                ·
                  refine ⟨1234653964123126625208685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646205285497502166944913 1234653964123126625208685)
                  ·
                    refine ⟨462995236546172484453257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234653964123126625208685 462995236546172484453257)
                    ·
                      refine ⟨347246427409629363339943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 462995236546172484453257 347246427409629363339943)
                      ·
                        rfl

theorem cell23_676260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_676260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676260 prefixEnd_676260 := by exact prefixLift 676260
  have htrace : WordTrace (prefixWord ++ tailWord_676260) baseStart_676260 baseEnd_676260 := by
    simpa [prefixWord, tailWord_676260, baseEnd_676260] using wordTrace_append hprefix tailTrace_676260
  have hstable : (prefixWord ++ tailWord_676260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676260).length < 2 ^ (prefixWord ++ tailWord_676260).sum := by decide
  have hdescent : baseEnd_676260 < baseStart_676260 := by decide
  rcases family_descends (prefixWord ++ tailWord_676260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676273 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_676273 : Nat := 118140960795 + 676273 * 2 ^ 59
def prefixEnd_676273 : Nat := 4983230072969 + 3 ^ 40 * 676273 * 2
def baseEnd_676273 : Nat := 347253102658137812477383

theorem tailTrace_676273 : CollatzResearch.WordTrace tailWord_676273 prefixEnd_676273 347253102658137812477383 := by
  unfold tailWord_676273
  simp only [CollatzResearch.WordTrace]
  refine ⟨24665702678985894078225473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16443801785990596052150315 24665702678985894078225473)
  ·
    refine ⟨18499277009239420558669105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24665702678985894078225473 18499277009239420558669105)
    ·
      refine ⟨13874457756929565419001829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18499277009239420558669105 13874457756929565419001829)
      ·
        refine ⟨2601460829424293516062843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13874457756929565419001829 2601460829424293516062843)
        ·
          refine ⟨3902191244136440274094265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601460829424293516062843 3902191244136440274094265)
          ·
            refine ⟨2926643433102330205570699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3902191244136440274094265 2926643433102330205570699)
            ·
              refine ⟨4389965149653495308356049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926643433102330205570699 4389965149653495308356049)
              ·
                refine ⟨3292473862240121481267037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389965149653495308356049 3292473862240121481267037)
                ·
                  refine ⟨1234677698340045555475139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3292473862240121481267037 1234677698340045555475139)
                  ·
                    refine ⟨1852016547510068333212709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234677698340045555475139 1852016547510068333212709)
                    ·
                      refine ⟨347253102658137812477383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1852016547510068333212709 347253102658137812477383)
                      ·
                        rfl

theorem cell23_676273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_676273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676273 prefixEnd_676273 := by exact prefixLift 676273
  have htrace : WordTrace (prefixWord ++ tailWord_676273) baseStart_676273 baseEnd_676273 := by
    simpa [prefixWord, tailWord_676273, baseEnd_676273] using wordTrace_append hprefix tailTrace_676273
  have hstable : (prefixWord ++ tailWord_676273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676273).length < 2 ^ (prefixWord ++ tailWord_676273).sum := by decide
  have hdescent : baseEnd_676273 < baseStart_676273 := by decide
  rcases family_descends (prefixWord ++ tailWord_676273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676310 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_676310 : Nat := 118140960795 + 676310 * 2 ^ 59
def prefixEnd_676310 : Nat := 4983230072969 + 3 ^ 40 * 676310 * 2
def baseEnd_676310 : Nat := 347272101442354167714713

theorem tailTrace_676310 : CollatzResearch.WordTrace tailWord_676310 prefixEnd_676310 347272101442354167714713 := by
  unfold tailWord_676310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541690761240740587332649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16444701453234566264881589 1541690761240740587332649)
  ·
    refine ⟨1156268070930555440499487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541690761240740587332649 1156268070930555440499487)
    ·
      refine ⟨1734402106395833160749231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156268070930555440499487 1734402106395833160749231)
      ·
        refine ⟨2601603159593749741123847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734402106395833160749231 2601603159593749741123847)
        ·
          refine ⟨3902404739390624611685771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601603159593749741123847 3902404739390624611685771)
          ·
            refine ⟨5853607109085936917528657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902404739390624611685771 5853607109085936917528657)
            ·
              refine ⟨4390205331814452688146493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853607109085936917528657 4390205331814452688146493)
              ·
                refine ⟨1646326999430419758054935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4390205331814452688146493 1646326999430419758054935)
                ·
                  refine ⟨2469490499145629637082403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646326999430419758054935 2469490499145629637082403)
                  ·
                    refine ⟨3704235748718444455623605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469490499145629637082403 3704235748718444455623605)
                    ·
                      refine ⟨347272101442354167714713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3704235748718444455623605 347272101442354167714713)
                      ·
                        rfl

theorem cell23_676310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_676310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676310 prefixEnd_676310 := by exact prefixLift 676310
  have htrace : WordTrace (prefixWord ++ tailWord_676310) baseStart_676310 baseEnd_676310 := by
    simpa [prefixWord, tailWord_676310, baseEnd_676310] using wordTrace_append hprefix tailTrace_676310
  have hstable : (prefixWord ++ tailWord_676310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676310).length < 2 ^ (prefixWord ++ tailWord_676310).sum := by decide
  have hdescent : baseEnd_676310 < baseStart_676310 := by decide
  rcases family_descends (prefixWord ++ tailWord_676310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676346 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_676346 : Nat := 118140960795 + 676346 * 2 ^ 59
def prefixEnd_676346 : Nat := 4983230072969 + 3 ^ 40 * 676346 * 2
def baseEnd_676346 : Nat := 347290586745916026864547

theorem tailTrace_676346 : CollatzResearch.WordTrace tailWord_676346 prefixEnd_676346 347290586745916026864547 := by
  unfold tailWord_676346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167091301930356886408223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16445576805147618363755261 6167091301930356886408223)
  ·
    refine ⟨9250636952895535329612335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167091301930356886408223 9250636952895535329612335)
    ·
      refine ⟨13875955429343302994418503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9250636952895535329612335 13875955429343302994418503)
      ·
        refine ⟨20813933144014954491627755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13875955429343302994418503 20813933144014954491627755)
        ·
          refine ⟨31220899716022431737441633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20813933144014954491627755 31220899716022431737441633)
          ·
            refine ⟨23415674787016823803081225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31220899716022431737441633 23415674787016823803081225)
            ·
              refine ⟨17561756090262617852310919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23415674787016823803081225 17561756090262617852310919)
              ·
                refine ⟨26342634135393926778466379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17561756090262617852310919 26342634135393926778466379)
                ·
                  refine ⟨39513951203090890167699569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26342634135393926778466379 39513951203090890167699569)
                  ·
                    refine ⟨29635463402318167625774677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39513951203090890167699569 29635463402318167625774677)
                    ·
                      refine ⟨347290586745916026864547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 29635463402318167625774677 347290586745916026864547)
                      ·
                        rfl

theorem cell23_676346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_676346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676346 prefixEnd_676346 := by exact prefixLift 676346
  have htrace : WordTrace (prefixWord ++ tailWord_676346) baseStart_676346 baseEnd_676346 := by
    simpa [prefixWord, tailWord_676346, baseEnd_676346] using wordTrace_append hprefix tailTrace_676346
  have hstable : (prefixWord ++ tailWord_676346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676346).length < 2 ^ (prefixWord ++ tailWord_676346).sum := by decide
  have hdescent : baseEnd_676346 < baseStart_676346 := by decide
  rcases family_descends (prefixWord ++ tailWord_676346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676353 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_676353 : Nat := 118140960795 + 676353 * 2 ^ 59
def prefixEnd_676353 : Nat := 4983230072969 + 3 ^ 40 * 676353 * 2
def baseEnd_676353 : Nat := 347294181110497499477015

theorem tailTrace_676353 : CollatzResearch.WordTrace tailWord_676353 prefixEnd_676353 347294181110497499477015 := by
  unfold tailWord_676353
  simp only [CollatzResearch.WordTrace]
  refine ⟨24668620518696067741137713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16445747012464045160758475 24668620518696067741137713)
  ·
    refine ⟨18501465389022050805853285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24668620518696067741137713 18501465389022050805853285)
    ·
      refine ⟨3469024760441634526097491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18501465389022050805853285 3469024760441634526097491)
      ·
        refine ⟨5203537140662451789146237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469024760441634526097491 5203537140662451789146237)
        ·
          refine ⟨1951326427748419420929839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5203537140662451789146237 1951326427748419420929839)
          ·
            refine ⟨2926989641622629131394759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951326427748419420929839 2926989641622629131394759)
            ·
              refine ⟨4390484462433943697092139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926989641622629131394759 4390484462433943697092139)
              ·
                refine ⟨6585726693650915545638209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390484462433943697092139 6585726693650915545638209)
                ·
                  refine ⟨4939295020238186659228657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6585726693650915545638209 4939295020238186659228657)
                  ·
                    refine ⟨3704471265178639994421493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939295020238186659228657 3704471265178639994421493)
                    ·
                      refine ⟨347294181110497499477015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3704471265178639994421493 347294181110497499477015)
                      ·
                        rfl

theorem cell23_676353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_676353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676353 prefixEnd_676353 := by exact prefixLift 676353
  have htrace : WordTrace (prefixWord ++ tailWord_676353) baseStart_676353 baseEnd_676353 := by
    simpa [prefixWord, tailWord_676353, baseEnd_676353] using wordTrace_append hprefix tailTrace_676353
  have hstable : (prefixWord ++ tailWord_676353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676353).length < 2 ^ (prefixWord ++ tailWord_676353).sum := by decide
  have hdescent : baseEnd_676353 < baseStart_676353 := by decide
  rcases family_descends (prefixWord ++ tailWord_676353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676383 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_676383 : Nat := 118140960795 + 676383 * 2 ^ 59
def prefixEnd_676383 : Nat := 4983230072969 + 3 ^ 40 * 676383 * 2
def baseEnd_676383 : Nat := 347309585530132382101877

theorem tailTrace_676383 : CollatzResearch.WordTrace tailWord_676383 prefixEnd_676383 347309585530132382101877 := by
  unfold tailWord_676383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669714708587382864729803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16446476472391588576486535 24669714708587382864729803)
  ·
    refine ⟨37004572062881074297094705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24669714708587382864729803 37004572062881074297094705)
    ·
      refine ⟨27753429047160805722821029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37004572062881074297094705 27753429047160805722821029)
      ·
        refine ⟨5203767946342651073028943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27753429047160805722821029 5203767946342651073028943)
        ·
          refine ⟨7805651919513976609543415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203767946342651073028943 7805651919513976609543415)
          ·
            refine ⟨11708477879270964914315123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805651919513976609543415 11708477879270964914315123)
            ·
              refine ⟨17562716818906447371472685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708477879270964914315123 17562716818906447371472685)
              ·
                refine ⟨6586018807089917764302257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17562716818906447371472685 6586018807089917764302257)
                ·
                  refine ⟨4939514105317438323226693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586018807089917764302257 4939514105317438323226693)
                  ·
                    refine ⟨926158894747019685605005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939514105317438323226693 926158894747019685605005)
                    ·
                      refine ⟨347309585530132382101877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926158894747019685605005 347309585530132382101877)
                      ·
                        rfl

theorem cell23_676383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_676383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676383 prefixEnd_676383 := by exact prefixLift 676383
  have htrace : WordTrace (prefixWord ++ tailWord_676383) baseStart_676383 baseEnd_676383 := by
    simpa [prefixWord, tailWord_676383, baseEnd_676383] using wordTrace_append hprefix tailTrace_676383
  have hstable : (prefixWord ++ tailWord_676383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676383).length < 2 ^ (prefixWord ++ tailWord_676383).sum := by decide
  have hdescent : baseEnd_676383 < baseStart_676383 := by decide
  rcases family_descends (prefixWord ++ tailWord_676383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676391 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_676391 : Nat := 118140960795 + 676391 * 2 ^ 59
def prefixEnd_676391 : Nat := 4983230072969 + 3 ^ 40 * 676391 * 2
def baseEnd_676391 : Nat := 347313693375368350801841

theorem tailTrace_676391 : CollatzResearch.WordTrace tailWord_676391 prefixEnd_676391 347313693375368350801841 := by
  unfold tailWord_676391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670006492558400231021027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16446670995038933487347351 24670006492558400231021027)
  ·
    refine ⟨37005009738837600346531541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24670006492558400231021027 37005009738837600346531541)
    ·
      refine ⟨867304915754006258121833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 37005009738837600346531541 867304915754006258121833)
      ·
        refine ⟨650478686815504693591375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867304915754006258121833 650478686815504693591375)
        ·
          refine ⟨975718030223257040387063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650478686815504693591375 975718030223257040387063)
          ·
            refine ⟨1463577045334885560580595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975718030223257040387063 1463577045334885560580595)
            ·
              refine ⟨2195365568002328340870893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463577045334885560580595 2195365568002328340870893)
              ·
                refine ⟨823262088000873127826585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195365568002328340870893 823262088000873127826585)
                ·
                  refine ⟨617446566000654845869939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823262088000873127826585 617446566000654845869939)
                  ·
                    refine ⟨926169849000982268804909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617446566000654845869939 926169849000982268804909)
                    ·
                      refine ⟨347313693375368350801841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926169849000982268804909 347313693375368350801841)
                      ·
                        rfl

theorem cell23_676391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_676391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676391 prefixEnd_676391 := by exact prefixLift 676391
  have htrace : WordTrace (prefixWord ++ tailWord_676391) baseStart_676391 baseEnd_676391 := by
    simpa [prefixWord, tailWord_676391, baseEnd_676391] using wordTrace_append hprefix tailTrace_676391
  have hstable : (prefixWord ++ tailWord_676391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676391).length < 2 ^ (prefixWord ++ tailWord_676391).sum := by decide
  have hdescent : baseEnd_676391 < baseStart_676391 := by decide
  rcases family_descends (prefixWord ++ tailWord_676391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676437 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 5]
def baseStart_676437 : Nat := 118140960795 + 676437 * 2 ^ 59
def prefixEnd_676437 : Nat := 4983230072969 + 3 ^ 40 * 676437 * 2
def baseEnd_676437 : Nat := 38593034831719463425181

theorem tailTrace_676437 : CollatzResearch.WordTrace tailWord_676437 prefixEnd_676437 38593034831719463425181 := by
  unfold tailWord_676437
  simp only [CollatzResearch.WordTrace]
  refine ⟨24671684250391750087195565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16447789500261166724797043 24671684250391750087195565)
  ·
    refine ⟨9251881593896906282698337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24671684250391750087195565 9251881593896906282698337)
    ·
      refine ⟨6938911195422679712023753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9251881593896906282698337 6938911195422679712023753)
      ·
        refine ⟨5204183396567009784017815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6938911195422679712023753 5204183396567009784017815)
        ·
          refine ⟨7806275094850514676026723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204183396567009784017815 7806275094850514676026723)
          ·
            refine ⟨11709412642275772014040085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806275094850514676026723 11709412642275772014040085)
            ·
              refine ⟨548878717606676813158129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11709412642275772014040085 548878717606676813158129)
              ·
                refine ⟨411659038205007609868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548878717606676813158129 411659038205007609868597)
                ·
                  refine ⟨38593034831719463425181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411659038205007609868597 38593034831719463425181)
                  ·
                    rfl

theorem cell23_676437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_676437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676437 prefixEnd_676437 := by exact prefixLift 676437
  have htrace : WordTrace (prefixWord ++ tailWord_676437) baseStart_676437 baseEnd_676437 := by
    simpa [prefixWord, tailWord_676437, baseEnd_676437] using wordTrace_append hprefix tailTrace_676437
  have hstable : (prefixWord ++ tailWord_676437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676437).length < 2 ^ (prefixWord ++ tailWord_676437).sum := by decide
  have hdescent : baseEnd_676437 < baseStart_676437 := by decide
  rcases family_descends (prefixWord ++ tailWord_676437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676440 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_676440 : Nat := 118140960795 + 676440 * 2 ^ 59
def prefixEnd_676440 : Nat := 4983230072969 + 3 ^ 40 * 676440 * 2
def baseEnd_676440 : Nat := 347338853927438659089115

theorem tailTrace_676440 : CollatzResearch.WordTrace tailWord_676440 prefixEnd_676440 347338853927438659089115 := by
  unfold tailWord_676440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335896834690440799777387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16447862446253921066369849 12335896834690440799777387)
  ·
    refine ⟨18503845252035661199666081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12335896834690440799777387 18503845252035661199666081)
    ·
      refine ⟨13877883939026745899749561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18503845252035661199666081 13877883939026745899749561)
      ·
        refine ⟨10408412954270059424812171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13877883939026745899749561 10408412954270059424812171)
        ·
          refine ⟨15612619431405089137218257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10408412954270059424812171 15612619431405089137218257)
          ·
            refine ⟨11709464573553816852913693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15612619431405089137218257 11709464573553816852913693)
            ·
              refine ⟨4391049215082681319842635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11709464573553816852913693 4391049215082681319842635)
              ·
                refine ⟨6586573822624021979763953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391049215082681319842635 6586573822624021979763953)
                ·
                  refine ⟨4939930366968016484822965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586573822624021979763953 4939930366968016484822965)
                  ·
                    refine ⟨463118471903251545452153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4939930366968016484822965 463118471903251545452153)
                    ·
                      refine ⟨347338853927438659089115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463118471903251545452153 347338853927438659089115)
                      ·
                        rfl

theorem cell23_676440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_676440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676440 prefixEnd_676440 := by exact prefixLift 676440
  have htrace : WordTrace (prefixWord ++ tailWord_676440) baseStart_676440 baseEnd_676440 := by
    simpa [prefixWord, tailWord_676440, baseEnd_676440] using wordTrace_append hprefix tailTrace_676440
  have hstable : (prefixWord ++ tailWord_676440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676440).length < 2 ^ (prefixWord ++ tailWord_676440).sum := by decide
  have hdescent : baseEnd_676440 < baseStart_676440 := by decide
  rcases family_descends (prefixWord ++ tailWord_676440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676482 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_676482 : Nat := 118140960795 + 676482 * 2 ^ 59
def prefixEnd_676482 : Nat := 4983230072969 + 3 ^ 40 * 676482 * 2
def baseEnd_676482 : Nat := 347360420114927494763923

theorem tailTrace_676482 : CollatzResearch.WordTrace tailWord_676482 prefixEnd_676482 347360420114927494763923 := by
  unfold tailWord_676482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168331383807180693145925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16448883690152481848389133 6168331383807180693145925)
  ·
    refine ⟨1156562134463846379964861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6168331383807180693145925 1156562134463846379964861)
    ·
      refine ⟨433710800423942392486823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1156562134463846379964861 433710800423942392486823)
      ·
        refine ⟨650566200635913588730235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433710800423942392486823 650566200635913588730235)
        ·
          refine ⟨975849300953870383095353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650566200635913588730235 975849300953870383095353)
          ·
            refine ⟨731886975715402787321515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975849300953870383095353 731886975715402787321515)
            ·
              refine ⟨1097830463573104180982273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731886975715402787321515 1097830463573104180982273)
              ·
                refine ⟨823372847679828135736705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097830463573104180982273 823372847679828135736705)
                ·
                  refine ⟨617529635759871101802529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823372847679828135736705 617529635759871101802529)
                  ·
                    refine ⟨463147226819903326351897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617529635759871101802529 463147226819903326351897)
                    ·
                      refine ⟨347360420114927494763923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463147226819903326351897 347360420114927494763923)
                      ·
                        rfl

theorem cell23_676482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_676482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676482 prefixEnd_676482 := by exact prefixLift 676482
  have htrace : WordTrace (prefixWord ++ tailWord_676482) baseStart_676482 baseEnd_676482 := by
    simpa [prefixWord, tailWord_676482, baseEnd_676482] using wordTrace_append hprefix tailTrace_676482
  have hstable : (prefixWord ++ tailWord_676482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676482).length < 2 ^ (prefixWord ++ tailWord_676482).sum := by decide
  have hdescent : baseEnd_676482 < baseStart_676482 := by decide
  rcases family_descends (prefixWord ++ tailWord_676482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676483 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_676483 : Nat := 118140960795 + 676483 * 2 ^ 59
def prefixEnd_676483 : Nat := 4983230072969 + 3 ^ 40 * 676483 * 2
def baseEnd_676483 : Nat := 347360933595581990851417

theorem tailTrace_676483 : CollatzResearch.WordTrace tailWord_676483 prefixEnd_676483 347360933595581990851417 := by
  unfold tailWord_676483
  simp only [CollatzResearch.WordTrace]
  refine ⟨24673362008225099943370103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16448908005483399962246735 24673362008225099943370103)
  ·
    refine ⟨37010043012337649915055155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24673362008225099943370103 37010043012337649915055155)
    ·
      refine ⟨55515064518506474872582733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37010043012337649915055155 55515064518506474872582733)
      ·
        refine ⟨20818149194439928077218525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55515064518506474872582733 20818149194439928077218525)
        ·
          refine ⟨7806805947914973028956947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20818149194439928077218525 7806805947914973028956947)
          ·
            refine ⟨11710208921872459543435421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806805947914973028956947 11710208921872459543435421)
            ·
              refine ⟨4391328345702172328788283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11710208921872459543435421 4391328345702172328788283)
              ·
                refine ⟨6586992518553258493182425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391328345702172328788283 6586992518553258493182425)
                ·
                  refine ⟨4940244388914943869886819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586992518553258493182425 4940244388914943869886819)
                  ·
                    refine ⟨7410366583372415804830229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4940244388914943869886819 7410366583372415804830229)
                    ·
                      refine ⟨347360933595581990851417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7410366583372415804830229 347360933595581990851417)
                      ·
                        rfl

theorem cell23_676483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_676483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676483 prefixEnd_676483 := by exact prefixLift 676483
  have htrace : WordTrace (prefixWord ++ tailWord_676483) baseStart_676483 baseEnd_676483 := by
    simpa [prefixWord, tailWord_676483, baseEnd_676483] using wordTrace_append hprefix tailTrace_676483
  have hstable : (prefixWord ++ tailWord_676483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676483).length < 2 ^ (prefixWord ++ tailWord_676483).sum := by decide
  have hdescent : baseEnd_676483 < baseStart_676483 := by decide
  rcases family_descends (prefixWord ++ tailWord_676483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676554 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_676554 : Nat := 118140960795 + 676554 * 2 ^ 59
def prefixEnd_676554 : Nat := 4983230072969 + 3 ^ 40 * 676554 * 2
def baseEnd_676554 : Nat := 347397390722051213063591

theorem tailTrace_676554 : CollatzResearch.WordTrace tailWord_676554 prefixEnd_676554 347397390722051213063591 := by
  unfold tailWord_676554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168987897741969767301179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16450634393978586046136477 6168987897741969767301179)
  ·
    refine ⟨9253481846612954650951769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168987897741969767301179 9253481846612954650951769)
    ·
      refine ⟨6940111384959715988213827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9253481846612954650951769 6940111384959715988213827)
      ·
        refine ⟨10410167077439573982320741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940111384959715988213827 10410167077439573982320741)
        ·
          refine ⟨1951906327019920121685139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10410167077439573982320741 1951906327019920121685139)
          ·
            refine ⟨2927859490529880182527709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951906327019920121685139 2927859490529880182527709)
            ·
              refine ⟨1097947308948705068447891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2927859490529880182527709 1097947308948705068447891)
              ·
                refine ⟨1646920963423057602671837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097947308948705068447891 1646920963423057602671837)
                ·
                  refine ⟨617595361283646601001939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1646920963423057602671837 617595361283646601001939)
                  ·
                    refine ⟨926393041925469901502909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617595361283646601001939 926393041925469901502909)
                    ·
                      refine ⟨347397390722051213063591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926393041925469901502909 347397390722051213063591)
                      ·
                        rfl

theorem cell23_676554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_676554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676554 prefixEnd_676554 := by exact prefixLift 676554
  have htrace : WordTrace (prefixWord ++ tailWord_676554) baseStart_676554 baseEnd_676554 := by
    simpa [prefixWord, tailWord_676554, baseEnd_676554] using wordTrace_append hprefix tailTrace_676554
  have hstable : (prefixWord ++ tailWord_676554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676554).length < 2 ^ (prefixWord ++ tailWord_676554).sum := by decide
  have hdescent : baseEnd_676554 < baseStart_676554 := by decide
  rcases family_descends (prefixWord ++ tailWord_676554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676570 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_676570 : Nat := 118140960795 + 676570 * 2 ^ 59
def prefixEnd_676570 : Nat := 4983230072969 + 3 ^ 40 * 676570 * 2
def baseEnd_676570 : Nat := 115801868804174383487839

theorem tailTrace_676570 : CollatzResearch.WordTrace tailWord_676570 prefixEnd_676570 115801868804174383487839 := by
  unfold tailWord_676570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169133789727478450446791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16451023439273275867858109 6169133789727478450446791)
  ·
    refine ⟨9253700684591217675670187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6169133789727478450446791 9253700684591217675670187)
    ·
      refine ⟨13880551026886826513505281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253700684591217675670187 13880551026886826513505281)
      ·
        refine ⟨10410413270165119885128961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13880551026886826513505281 10410413270165119885128961)
        ·
          refine ⟨7807809952623839913846721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10410413270165119885128961 7807809952623839913846721)
          ·
            refine ⟨5855857464467879935385041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7807809952623839913846721 5855857464467879935385041)
            ·
              refine ⟨4391893098350909951538781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855857464467879935385041 4391893098350909951538781)
              ·
                refine ⟨1646959911881591231827043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4391893098350909951538781 1646959911881591231827043)
                ·
                  refine ⟨2470439867822386847740565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646959911881591231827043 2470439867822386847740565)
                  ·
                    refine ⟨115801868804174383487839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2470439867822386847740565 115801868804174383487839)
                    ·
                      rfl

theorem cell23_676570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_676570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676570 prefixEnd_676570 := by exact prefixLift 676570
  have htrace : WordTrace (prefixWord ++ tailWord_676570) baseStart_676570 baseEnd_676570 := by
    simpa [prefixWord, tailWord_676570, baseEnd_676570] using wordTrace_append hprefix tailTrace_676570
  have hstable : (prefixWord ++ tailWord_676570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676570).length < 2 ^ (prefixWord ++ tailWord_676570).sum := by decide
  have hdescent : baseEnd_676570 < baseStart_676570 := by decide
  rcases family_descends (prefixWord ++ tailWord_676570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676577 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_676577 : Nat := 118140960795 + 676577 * 2 ^ 59
def prefixEnd_676577 : Nat := 4983230072969 + 3 ^ 40 * 676577 * 2
def baseEnd_676577 : Nat := 347409200777104623075985

theorem tailTrace_676577 : CollatzResearch.WordTrace tailWord_676577 prefixEnd_676577 347409200777104623075985 := by
  unfold tailWord_676577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24676790469884553997291985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16451193646589702664861323 24676790469884553997291985)
  ·
    refine ⟨18507592852413415497968989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24676790469884553997291985 18507592852413415497968989)
    ·
      refine ⟨6940347319655030811738371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18507592852413415497968989 6940347319655030811738371)
      ·
        refine ⟨10410520979482546217607557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940347319655030811738371 10410520979482546217607557)
        ·
          refine ⟨1951972683652977415801417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10410520979482546217607557 1951972683652977415801417)
          ·
            refine ⟨1463979512739733061851063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951972683652977415801417 1463979512739733061851063)
            ·
              refine ⟨2195969269109599592776595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463979512739733061851063 2195969269109599592776595)
              ·
                refine ⟨3293953903664399389164893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195969269109599592776595 3293953903664399389164893)
                ·
                  refine ⟨1235232713874149770936835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3293953903664399389164893 1235232713874149770936835)
                  ·
                    refine ⟨1852849070811224656405253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235232713874149770936835 1852849070811224656405253)
                    ·
                      refine ⟨347409200777104623075985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1852849070811224656405253 347409200777104623075985)
                      ·
                        rfl

theorem cell23_676577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_676577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676577 prefixEnd_676577 := by exact prefixLift 676577
  have htrace : WordTrace (prefixWord ++ tailWord_676577) baseStart_676577 baseEnd_676577 := by
    simpa [prefixWord, tailWord_676577, baseEnd_676577] using wordTrace_append hprefix tailTrace_676577
  have hstable : (prefixWord ++ tailWord_676577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676577).length < 2 ^ (prefixWord ++ tailWord_676577).sum := by decide
  have hdescent : baseEnd_676577 < baseStart_676577 := by decide
  rcases family_descends (prefixWord ++ tailWord_676577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676604 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_676604 : Nat := 118140960795 + 676604 * 2 ^ 59
def prefixEnd_676604 : Nat := 4983230072969 + 3 ^ 40 * 676604 * 2
def baseEnd_676604 : Nat := 115807688251592005812787

theorem tailTrace_676604 : CollatzResearch.WordTrace tailWord_676604 prefixEnd_676604 115807688251592005812787 := by
  unfold tailWord_676604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338887620393368804262433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16451850160524491739016577 12338887620393368804262433)
  ·
    refine ⟨9254165715295026603196825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12338887620393368804262433 9254165715295026603196825)
    ·
      refine ⟨6940624286471269952397619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9254165715295026603196825 6940624286471269952397619)
      ·
        refine ⟨10410936429706904928596429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940624286471269952397619 10410936429706904928596429)
        ·
          refine ⟨3904101161140089348223661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10410936429706904928596429 3904101161140089348223661)
          ·
            refine ⟨1464037935427533505583873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3904101161140089348223661 1464037935427533505583873)
            ·
              refine ⟨1098028451570650129187905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464037935427533505583873 1098028451570650129187905)
              ·
                refine ⟨823521338677987596890929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098028451570650129187905 823521338677987596890929)
                ·
                  refine ⟨617641004008490697668197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823521338677987596890929 617641004008490697668197)
                  ·
                    refine ⟨115807688251592005812787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617641004008490697668197 115807688251592005812787)
                    ·
                      rfl

theorem cell23_676604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_676604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676604 prefixEnd_676604 := by exact prefixLift 676604
  have htrace : WordTrace (prefixWord ++ tailWord_676604) baseStart_676604 baseEnd_676604 := by
    simpa [prefixWord, tailWord_676604, baseEnd_676604] using wordTrace_append hprefix tailTrace_676604
  have hstable : (prefixWord ++ tailWord_676604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676604).length < 2 ^ (prefixWord ++ tailWord_676604).sum := by decide
  have hdescent : baseEnd_676604 < baseStart_676604 := by decide
  rcases family_descends (prefixWord ++ tailWord_676604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676627 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3]
def baseStart_676627 : Nat := 118140960795 + 676627 * 2 ^ 59
def prefixEnd_676627 : Nat := 4983230072969 + 3 ^ 40 * 676627 * 2
def baseEnd_676627 : Nat := 347434874809829427450755

theorem tailTrace_676627 : CollatzResearch.WordTrace tailWord_676627 prefixEnd_676627 347434874809829427450755 := by
  unfold tailWord_676627
  simp only [CollatzResearch.WordTrace]
  refine ⟨24678614119703412536612135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16452409413135608357741423 24678614119703412536612135)
  ·
    refine ⟨37017921179555118804918203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24678614119703412536612135 37017921179555118804918203)
    ·
      refine ⟨55526881769332678207377305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37017921179555118804918203 55526881769332678207377305)
      ·
        refine ⟨41645161326999508655532979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55526881769332678207377305 41645161326999508655532979)
        ·
          refine ⟨62467741990499262983299469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41645161326999508655532979 62467741990499262983299469)
          ·
            refine ⟨23425403246437223618737301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62467741990499262983299469 23425403246437223618737301)
            ·
              refine ⟨1098065777176744857128311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23425403246437223618737301 1098065777176744857128311)
              ·
                refine ⟨1647098665765117285692467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098065777176744857128311 1647098665765117285692467)
                ·
                  refine ⟨2470647998647675928538701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647098665765117285692467 2470647998647675928538701)
                  ·
                    refine ⟨926492999492878473202013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470647998647675928538701 926492999492878473202013)
                    ·
                      refine ⟨347434874809829427450755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926492999492878473202013 347434874809829427450755)
                      ·
                        rfl

theorem cell23_676627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_676627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676627 prefixEnd_676627 := by exact prefixLift 676627
  have htrace : WordTrace (prefixWord ++ tailWord_676627) baseStart_676627 baseEnd_676627 := by
    simpa [prefixWord, tailWord_676627, baseEnd_676627] using wordTrace_append hprefix tailTrace_676627
  have hstable : (prefixWord ++ tailWord_676627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676627).length < 2 ^ (prefixWord ++ tailWord_676627).sum := by decide
  have hdescent : baseEnd_676627 < baseStart_676627 := by decide
  rcases family_descends (prefixWord ++ tailWord_676627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676661 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_676661 : Nat := 118140960795 + 676661 * 2 ^ 59
def prefixEnd_676661 : Nat := 4983230072969 + 3 ^ 40 * 676661 * 2
def baseEnd_676661 : Nat := 347452333152082294425599

theorem tailTrace_676661 : CollatzResearch.WordTrace tailWord_676661 prefixEnd_676661 347452333152082294425599 := by
  unfold tailWord_676661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679854201580236343349837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16453236134386824228899891 24679854201580236343349837)
  ·
    refine ⟨9254945325592588628756189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24679854201580236343349837 9254945325592588628756189)
    ·
      refine ⟨3470604497097220735783571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9254945325592588628756189 3470604497097220735783571)
      ·
        refine ⟨5205906745645831103675357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3470604497097220735783571 5205906745645831103675357)
        ·
          refine ⟨1952215029617186663878259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5205906745645831103675357 1952215029617186663878259)
          ·
            refine ⟨2928322544425779995817389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952215029617186663878259 2928322544425779995817389)
            ·
              refine ⟨1098120954159667498431521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2928322544425779995817389 1098120954159667498431521)
              ·
                refine ⟨823590715619750623823641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098120954159667498431521 823590715619750623823641)
                ·
                  refine ⟨617693036714812967867731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823590715619750623823641 617693036714812967867731)
                  ·
                    refine ⟨926539555072219451801597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617693036714812967867731 926539555072219451801597)
                    ·
                      refine ⟨347452333152082294425599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926539555072219451801597 347452333152082294425599)
                      ·
                        rfl

theorem cell23_676661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_676661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676661 prefixEnd_676661 := by exact prefixLift 676661
  have htrace : WordTrace (prefixWord ++ tailWord_676661) baseStart_676661 baseEnd_676661 := by
    simpa [prefixWord, tailWord_676661, baseEnd_676661] using wordTrace_append hprefix tailTrace_676661
  have hstable : (prefixWord ++ tailWord_676661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676661).length < 2 ^ (prefixWord ++ tailWord_676661).sum := by decide
  have hdescent : baseEnd_676661 < baseStart_676661 := by decide
  rcases family_descends (prefixWord ++ tailWord_676661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676775 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 5]
def baseStart_676775 : Nat := 118140960795 + 676775 * 2 ^ 59
def prefixEnd_676775 : Nat := 4983230072969 + 3 ^ 40 * 676775 * 2
def baseEnd_676775 : Nat := 38612318882966094266675

theorem tailTrace_676775 : CollatzResearch.WordTrace tailWord_676775 prefixEnd_676775 38612318882966094266675 := by
  unfold tailWord_676775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24684012123167233812999779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16456008082111489208666519 24684012123167233812999779)
  ·
    refine ⟨37026018184750850719499669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24684012123167233812999779 37026018184750850719499669)
    ·
      refine ⟨1735594602410196127476547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37026018184750850719499669 1735594602410196127476547)
      ·
        refine ⟨2603391903615294191214821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735594602410196127476547 2603391903615294191214821)
        ·
          refine ⟨488135981927867660852779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2603391903615294191214821 488135981927867660852779)
          ·
            refine ⟨732203972891801491279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488135981927867660852779 732203972891801491279169)
            ·
              refine ⟨549152979668851118459377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732203972891801491279169 549152979668851118459377)
              ·
                refine ⟨411864734751638338844533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549152979668851118459377 411864734751638338844533)
                ·
                  refine ⟨38612318882966094266675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411864734751638338844533 38612318882966094266675)
                  ·
                    rfl

theorem cell23_676775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 5].length) (baseStart_676775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676775 prefixEnd_676775 := by exact prefixLift 676775
  have htrace : WordTrace (prefixWord ++ tailWord_676775) baseStart_676775 baseEnd_676775 := by
    simpa [prefixWord, tailWord_676775, baseEnd_676775] using wordTrace_append hprefix tailTrace_676775
  have hstable : (prefixWord ++ tailWord_676775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676775).length < 2 ^ (prefixWord ++ tailWord_676775).sum := by decide
  have hdescent : baseEnd_676775 < baseStart_676775 := by decide
  rcases family_descends (prefixWord ++ tailWord_676775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676808 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_676808 : Nat := 118140960795 + 676808 * 2 ^ 59
def prefixEnd_676808 : Nat := 4983230072969 + 3 ^ 40 * 676808 * 2
def baseEnd_676808 : Nat := 347527814808293219287423

theorem tailTrace_676808 : CollatzResearch.WordTrace tailWord_676808 prefixEnd_676808 347527814808293219287423 := by
  unfold tailWord_676808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342607866023840224475539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16456810488031786965967385 12342607866023840224475539)
  ·
    refine ⟨18513911799035760336713309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12342607866023840224475539 18513911799035760336713309)
    ·
      refine ⟨6942716924638410126267491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18513911799035760336713309 6942716924638410126267491)
      ·
        refine ⟨10414075386957615189401237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6942716924638410126267491 10414075386957615189401237)
        ·
          refine ⟨488159783763638212003183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10414075386957615189401237 488159783763638212003183)
          ·
            refine ⟨732239675645457318004775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488159783763638212003183 732239675645457318004775)
            ·
              refine ⟨1098359513468185977007163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732239675645457318004775 1098359513468185977007163)
              ·
                refine ⟨1647539270202278965510745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098359513468185977007163 1647539270202278965510745)
                ·
                  refine ⟨1235654452651709224133059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647539270202278965510745 1235654452651709224133059)
                  ·
                    refine ⟨1853481678977563836199589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235654452651709224133059 1853481678977563836199589)
                    ·
                      refine ⟨347527814808293219287423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1853481678977563836199589 347527814808293219287423)
                      ·
                        rfl

theorem cell23_676808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_676808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676808 prefixEnd_676808 := by exact prefixLift 676808
  have htrace : WordTrace (prefixWord ++ tailWord_676808) baseStart_676808 baseEnd_676808 := by
    simpa [prefixWord, tailWord_676808, baseEnd_676808] using wordTrace_append hprefix tailTrace_676808
  have hstable : (prefixWord ++ tailWord_676808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676808).length < 2 ^ (prefixWord ++ tailWord_676808).sum := by decide
  have hdescent : baseEnd_676808 < baseStart_676808 := by decide
  rcases family_descends (prefixWord ++ tailWord_676808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676811 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 3]
def baseStart_676811 : Nat := 118140960795 + 676811 * 2 ^ 59
def prefixEnd_676811 : Nat := 4983230072969 + 3 ^ 40 * 676811 * 2
def baseEnd_676811 : Nat := 347529355250256707549909

theorem tailTrace_676811 : CollatzResearch.WordTrace tailWord_676811 prefixEnd_676811 347529355250256707549909 := by
  unfold tailWord_676811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24685325151036811961310287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16456883434024541307540191 24685325151036811961310287)
  ·
    refine ⟨37027987726555217941965431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24685325151036811961310287 37027987726555217941965431)
    ·
      refine ⟨55541981589832826912948147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37027987726555217941965431 55541981589832826912948147)
      ·
        refine ⟨83312972384749240369422221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55541981589832826912948147 83312972384749240369422221)
        ·
          refine ⟨31242364644280965138533333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83312972384749240369422221 31242364644280965138533333)
          ·
            refine ⟨732242921350335120434375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31242364644280965138533333 732242921350335120434375)
            ·
              refine ⟨1098364382025502680651563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732242921350335120434375 1098364382025502680651563)
              ·
                refine ⟨1647546573038254020977345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098364382025502680651563 1647546573038254020977345)
                ·
                  refine ⟨1235659929778690515733009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647546573038254020977345 1235659929778690515733009)
                  ·
                    refine ⟨926744947334017886799757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1235659929778690515733009 926744947334017886799757)
                    ·
                      refine ⟨347529355250256707549909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926744947334017886799757 347529355250256707549909)
                      ·
                        rfl

theorem cell23_676811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 2, 3].length) (baseStart_676811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676811 prefixEnd_676811 := by exact prefixLift 676811
  have htrace : WordTrace (prefixWord ++ tailWord_676811) baseStart_676811 baseEnd_676811 := by
    simpa [prefixWord, tailWord_676811, baseEnd_676811] using wordTrace_append hprefix tailTrace_676811
  have hstable : (prefixWord ++ tailWord_676811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676811).length < 2 ^ (prefixWord ++ tailWord_676811).sum := by decide
  have hdescent : baseEnd_676811 < baseStart_676811 := by decide
  rcases family_descends (prefixWord ++ tailWord_676811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676818 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_676818 : Nat := 118140960795 + 676818 * 2 ^ 59
def prefixEnd_676818 : Nat := 4983230072969 + 3 ^ 40 * 676818 * 2
def baseEnd_676818 : Nat := 115844316538279393387459

theorem tailTrace_676818 : CollatzResearch.WordTrace tailWord_676818 prefixEnd_676818 115844316538279393387459 := by
  unfold tailWord_676818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171395115502863039203777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16457053641340968104543405 6171395115502863039203777)
  ·
    refine ⟨4628546336627147279402833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6171395115502863039203777 4628546336627147279402833)
    ·
      refine ⟨3471409752470360459552125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4628546336627147279402833 3471409752470360459552125)
      ·
        refine ⟨1301778657176385172332047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3471409752470360459552125 1301778657176385172332047)
        ·
          refine ⟨1952667985764577758498071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301778657176385172332047 1952667985764577758498071)
          ·
            refine ⟨2929001978646866637747107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952667985764577758498071 2929001978646866637747107)
            ·
              refine ⟨4393502967970299956620661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929001978646866637747107 4393502967970299956620661)
              ·
                refine ⟨411890903247215620933187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4393502967970299956620661 411890903247215620933187)
                ·
                  refine ⟨617836354870823431399781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411890903247215620933187 617836354870823431399781)
                  ·
                    refine ⟨115844316538279393387459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 617836354870823431399781 115844316538279393387459)
                    ·
                      rfl

theorem cell23_676818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_676818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676818 prefixEnd_676818 := by exact prefixLift 676818
  have htrace : WordTrace (prefixWord ++ tailWord_676818) baseStart_676818 baseEnd_676818 := by
    simpa [prefixWord, tailWord_676818, baseEnd_676818] using wordTrace_append hprefix tailTrace_676818
  have hstable : (prefixWord ++ tailWord_676818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676818).length < 2 ^ (prefixWord ++ tailWord_676818).sum := by decide
  have hdescent : baseEnd_676818 < baseStart_676818 := by decide
  rcases family_descends (prefixWord ++ tailWord_676818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676831 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 6]
def baseStart_676831 : Nat := 118140960795 + 676831 * 2 ^ 59
def prefixEnd_676831 : Nat := 4983230072969 + 3 ^ 40 * 676831 * 2
def baseEnd_676831 : Nat := 38615513873705181033313

theorem tailTrace_676831 : CollatzResearch.WordTrace tailWord_676831 prefixEnd_676831 38615513873705181033313 := by
  unfold tailWord_676831
  simp only [CollatzResearch.WordTrace]
  refine ⟨24686054610964355377038347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16457369740642903584692231 24686054610964355377038347)
  ·
    refine ⟨37029081916446533065557521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24686054610964355377038347 37029081916446533065557521)
    ·
      refine ⟨27771811437334899799168141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37029081916446533065557521 27771811437334899799168141)
      ·
        refine ⟨10414429289000587424688053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27771811437334899799168141 10414429289000587424688053)
        ·
          refine ⟨976352745843805071064505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10414429289000587424688053 976352745843805071064505)
          ·
            refine ⟨732264559382853803298379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976352745843805071064505 732264559382853803298379)
            ·
              refine ⟨1098396839074280704947569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732264559382853803298379 1098396839074280704947569)
              ·
                refine ⟨823797629305710528710677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098396839074280704947569 823797629305710528710677)
                ·
                  refine ⟨38615513873705181033313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 823797629305710528710677 38615513873705181033313)
                  ·
                    rfl

theorem cell23_676831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 6].length) (baseStart_676831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676831 prefixEnd_676831 := by exact prefixLift 676831
  have htrace : WordTrace (prefixWord ++ tailWord_676831) baseStart_676831 baseEnd_676831 := by
    simpa [prefixWord, tailWord_676831, baseEnd_676831] using wordTrace_append hprefix tailTrace_676831
  have hstable : (prefixWord ++ tailWord_676831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676831).length < 2 ^ (prefixWord ++ tailWord_676831).sum := by decide
  have hdescent : baseEnd_676831 < baseStart_676831 := by decide
  rcases family_descends (prefixWord ++ tailWord_676831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676875 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 1, 1, 3]
def baseStart_676875 : Nat := 118140960795 + 676875 * 2 ^ 59
def prefixEnd_676875 : Nat := 4983230072969 + 3 ^ 40 * 676875 * 2
def baseEnd_676875 : Nat := 347562218012144457149615

theorem tailTrace_676875 : CollatzResearch.WordTrace tailWord_676875 prefixEnd_676875 347562218012144457149615 := by
  unfold tailWord_676875
  simp only [CollatzResearch.WordTrace]
  refine ⟨24687659422804950891640079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16458439615203300594426719 24687659422804950891640079)
  ·
    refine ⟨37031489134207426337460119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24687659422804950891640079 37031489134207426337460119)
    ·
      refine ⟨55547233701311139506190179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37031489134207426337460119 55547233701311139506190179)
      ·
        refine ⟨83320850551966709259285269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55547233701311139506190179 83320850551966709259285269)
        ·
          refine ⟨3905664869623439496528997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83320850551966709259285269 3905664869623439496528997)
          ·
            refine ⟨732312163054394905599187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3905664869623439496528997 732312163054394905599187)
            ·
              refine ⟨1098468244581592358398781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732312163054394905599187 1098468244581592358398781)
              ·
                refine ⟨411925591718097134399543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098468244581592358398781 411925591718097134399543)
                ·
                  refine ⟨617888387577145701599315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411925591718097134399543 617888387577145701599315)
                  ·
                    refine ⟨926832581365718552398973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617888387577145701599315 926832581365718552398973)
                    ·
                      refine ⟨347562218012144457149615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926832581365718552398973 347562218012144457149615)
                      ·
                        rfl

theorem cell23_676875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 1, 3].length) (baseStart_676875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676875 prefixEnd_676875 := by exact prefixLift 676875
  have htrace : WordTrace (prefixWord ++ tailWord_676875) baseStart_676875 baseEnd_676875 := by
    simpa [prefixWord, tailWord_676875, baseEnd_676875] using wordTrace_append hprefix tailTrace_676875
  have hstable : (prefixWord ++ tailWord_676875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676875).length < 2 ^ (prefixWord ++ tailWord_676875).sum := by decide
  have hdescent : baseEnd_676875 < baseStart_676875 := by decide
  rcases family_descends (prefixWord ++ tailWord_676875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676881 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_676881 : Nat := 118140960795 + 676881 * 2 ^ 59
def prefixEnd_676881 : Nat := 4983230072969 + 3 ^ 40 * 676881 * 2
def baseEnd_676881 : Nat := 347565298896071433674587

theorem tailTrace_676881 : CollatzResearch.WordTrace tailWord_676881 prefixEnd_676881 347565298896071433674587 := by
  unfold tailWord_676881
  simp only [CollatzResearch.WordTrace]
  refine ⟨24687878260783213916358497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16458585507188809277572331 24687878260783213916358497)
  ·
    refine ⟨18515908695587410437268873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24687878260783213916358497 18515908695587410437268873)
    ·
      refine ⟨13886931521690557827951655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18515908695587410437268873 13886931521690557827951655)
      ·
        refine ⟨20830397282535836741927483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13886931521690557827951655 20830397282535836741927483)
        ·
          refine ⟨31245595923803755112891225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20830397282535836741927483 31245595923803755112891225)
          ·
            refine ⟨23434196942852816334668419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31245595923803755112891225 23434196942852816334668419)
            ·
              refine ⟨35151295414279224502002629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23434196942852816334668419 35151295414279224502002629)
              ·
                refine ⟨6590867890177354594125493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35151295414279224502002629 6590867890177354594125493)
                ·
                  refine ⟨617893864704126993199265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6590867890177354594125493 617893864704126993199265)
                  ·
                    refine ⟨463420398528095244899449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617893864704126993199265 463420398528095244899449)
                    ·
                      refine ⟨347565298896071433674587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463420398528095244899449 347565298896071433674587)
                      ·
                        rfl

theorem cell23_676881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_676881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676881 prefixEnd_676881 := by exact prefixLift 676881
  have htrace : WordTrace (prefixWord ++ tailWord_676881) baseStart_676881 baseEnd_676881 := by
    simpa [prefixWord, tailWord_676881, baseEnd_676881] using wordTrace_append hprefix tailTrace_676881
  have hstable : (prefixWord ++ tailWord_676881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676881).length < 2 ^ (prefixWord ++ tailWord_676881).sum := by decide
  have hdescent : baseEnd_676881 < baseStart_676881 := by decide
  rcases family_descends (prefixWord ++ tailWord_676881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676892 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_676892 : Nat := 118140960795 + 676892 * 2 ^ 59
def prefixEnd_676892 : Nat := 4983230072969 + 3 ^ 40 * 676892 * 2
def baseEnd_676892 : Nat := 347570947183270890637037

theorem tailTrace_676892 : CollatzResearch.WordTrace tailWord_676892 prefixEnd_676892 347570947183270890637037 := by
  unfold tailWord_676892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344139731871681397504465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16458852975828908530005953 12344139731871681397504465)
  ·
    refine ⟨9258104798903761048128349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12344139731871681397504465 9258104798903761048128349)
    ·
      refine ⟨3471789299588910393048131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9258104798903761048128349 3471789299588910393048131)
      ·
        refine ⟨5207683949383365589572197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471789299588910393048131 5207683949383365589572197)
        ·
          refine ⟨976440740509381048044787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5207683949383365589572197 976440740509381048044787)
          ·
            refine ⟨1464661110764071572067181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976440740509381048044787 1464661110764071572067181)
            ·
              refine ⟨549247916536526839525193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1464661110764071572067181 549247916536526839525193)
              ·
                refine ⟨411935937402395129643895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549247916536526839525193 411935937402395129643895)
                ·
                  refine ⟨617903906103592694465843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411935937402395129643895 617903906103592694465843)
                  ·
                    refine ⟨926855859155389041698765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617903906103592694465843 926855859155389041698765)
                    ·
                      refine ⟨347570947183270890637037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926855859155389041698765 347570947183270890637037)
                      ·
                        rfl

theorem cell23_676892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_676892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676892 prefixEnd_676892 := by exact prefixLift 676892
  have htrace : WordTrace (prefixWord ++ tailWord_676892) baseStart_676892 baseEnd_676892 := by
    simpa [prefixWord, tailWord_676892, baseEnd_676892] using wordTrace_append hprefix tailTrace_676892
  have hstable : (prefixWord ++ tailWord_676892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676892).length < 2 ^ (prefixWord ++ tailWord_676892).sum := by decide
  have hdescent : baseEnd_676892 < baseStart_676892 := by decide
  rcases family_descends (prefixWord ++ tailWord_676892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676907 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_676907 : Nat := 118140960795 + 676907 * 2 ^ 59
def prefixEnd_676907 : Nat := 4983230072969 + 3 ^ 40 * 676907 * 2
def baseEnd_676907 : Nat := 347578649393088331949467

theorem tailTrace_676907 : CollatzResearch.WordTrace tailWord_676907 prefixEnd_676907 347578649393088331949467 := by
  unfold tailWord_676907
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688826558689020356804975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16459217705792680237869983 24688826558689020356804975)
  ·
    refine ⟨37033239838033530535207463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24688826558689020356804975 37033239838033530535207463)
    ·
      refine ⟨55549859757050295802811195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37033239838033530535207463 55549859757050295802811195)
      ·
        refine ⟨83324789635575443704216793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55549859757050295802811195 83324789635575443704216793)
        ·
          refine ⟨62493592226681582778162595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83324789635575443704216793 62493592226681582778162595)
          ·
            refine ⟨93740388340022374167243893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62493592226681582778162595 93740388340022374167243893)
            ·
              refine ⟨8788161406877097578179115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93740388340022374167243893 8788161406877097578179115)
              ·
                refine ⟨13182242110315646367268673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8788161406877097578179115 13182242110315646367268673)
                ·
                  refine ⟨9886681582736734775451505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13182242110315646367268673 9886681582736734775451505)
                  ·
                    refine ⟨7415011187052551081588629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9886681582736734775451505 7415011187052551081588629)
                    ·
                      refine ⟨347578649393088331949467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7415011187052551081588629 347578649393088331949467)
                      ·
                        rfl

theorem cell23_676907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_676907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676907 prefixEnd_676907 := by exact prefixLift 676907
  have htrace : WordTrace (prefixWord ++ tailWord_676907) baseStart_676907 baseEnd_676907 := by
    simpa [prefixWord, tailWord_676907, baseEnd_676907] using wordTrace_append hprefix tailTrace_676907
  have hstable : (prefixWord ++ tailWord_676907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676907).length < 2 ^ (prefixWord ++ tailWord_676907).sum := by decide
  have hdescent : baseEnd_676907 < baseStart_676907 := by decide
  rcases family_descends (prefixWord ++ tailWord_676907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676918 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_676918 : Nat := 118140960795 + 676918 * 2 ^ 59
def prefixEnd_676918 : Nat := 4983230072969 + 3 ^ 40 * 676918 * 2
def baseEnd_676918 : Nat := 347584297680287788911917

theorem tailTrace_676918 : CollatzResearch.WordTrace tailWord_676918 prefixEnd_676918 347584297680287788911917 := by
  unfold tailWord_676918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543076735103073077215963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16459485174432779490303605 1543076735103073077215963)
  ·
    refine ⟨2314615102654609615823945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543076735103073077215963 2314615102654609615823945)
    ·
      refine ⟨1735961326990957211867959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2314615102654609615823945 1735961326990957211867959)
      ·
        refine ⟨2603941990486435817801939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735961326990957211867959 2603941990486435817801939)
        ·
          refine ⟨3905912985729653726702909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603941990486435817801939 3905912985729653726702909)
          ·
            refine ⟨1464717369648620147513591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3905912985729653726702909 1464717369648620147513591)
            ·
              refine ⟨2197076054472930221270387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464717369648620147513591 2197076054472930221270387)
              ·
                refine ⟨3295614081709395331905581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197076054472930221270387 3295614081709395331905581)
                ·
                  refine ⟨1235855280641023249464593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3295614081709395331905581 1235855280641023249464593)
                  ·
                    refine ⟨926891460480767437098445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1235855280641023249464593 926891460480767437098445)
                    ·
                      refine ⟨347584297680287788911917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926891460480767437098445 347584297680287788911917)
                      ·
                        rfl

theorem cell23_676918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_676918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676918 prefixEnd_676918 := by exact prefixLift 676918
  have htrace : WordTrace (prefixWord ++ tailWord_676918) baseStart_676918 baseEnd_676918 := by
    simpa [prefixWord, tailWord_676918, baseEnd_676918] using wordTrace_append hprefix tailTrace_676918
  have hstable : (prefixWord ++ tailWord_676918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676918).length < 2 ^ (prefixWord ++ tailWord_676918).sum := by decide
  have hdescent : baseEnd_676918 < baseStart_676918 := by decide
  rcases family_descends (prefixWord ++ tailWord_676918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676948 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_676948 : Nat := 118140960795 + 676948 * 2 ^ 59
def prefixEnd_676948 : Nat := 4983230072969 + 3 ^ 40 * 676948 * 2
def baseEnd_676948 : Nat := 347599702099922671536779

theorem tailTrace_676948 : CollatzResearch.WordTrace tailWord_676948 prefixEnd_676948 347599702099922671536779 := by
  unfold tailWord_676948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345160975770242179523749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16460214634360322906031665 12345160975770242179523749)
  ·
    refine ⟨2314717682956920408660703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12345160975770242179523749 2314717682956920408660703)
    ·
      refine ⟨3472076524435380612991055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314717682956920408660703 3472076524435380612991055)
      ·
        refine ⟨5208114786653070919486583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472076524435380612991055 5208114786653070919486583)
        ·
          refine ⟨7812172179979606379229875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208114786653070919486583 7812172179979606379229875)
          ·
            refine ⟨11718258269969409568844813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7812172179979606379229875 11718258269969409568844813)
            ·
              refine ⟨4394346851238528588316805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11718258269969409568844813 4394346851238528588316805)
              ·
                refine ⟨823940034607224110309401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4394346851238528588316805 823940034607224110309401)
                ·
                  refine ⟨617955025955418082732051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823940034607224110309401 617955025955418082732051)
                  ·
                    refine ⟨926932538933127124098077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617955025955418082732051 926932538933127124098077)
                    ·
                      refine ⟨347599702099922671536779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 926932538933127124098077 347599702099922671536779)
                      ·
                        rfl

theorem cell23_676948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_676948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676948 prefixEnd_676948 := by exact prefixLift 676948
  have htrace : WordTrace (prefixWord ++ tailWord_676948) baseStart_676948 baseEnd_676948 := by
    simpa [prefixWord, tailWord_676948, baseEnd_676948] using wordTrace_append hprefix tailTrace_676948
  have hstable : (prefixWord ++ tailWord_676948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676948).length < 2 ^ (prefixWord ++ tailWord_676948).sum := by decide
  have hdescent : baseEnd_676948 < baseStart_676948 := by decide
  rcases family_descends (prefixWord ++ tailWord_676948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_676988 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_676988 : Nat := 118140960795 + 676988 * 2 ^ 59
def prefixEnd_676988 : Nat := 4983230072969 + 3 ^ 40 * 676988 * 2
def baseEnd_676988 : Nat := 347620241326102515036595

theorem tailTrace_676988 : CollatzResearch.WordTrace tailWord_676988 prefixEnd_676988 347620241326102515036595 := by
  unfold tailWord_676988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345890435697785595251809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16461187247597047460335745 12345890435697785595251809)
  ·
    refine ⟨9259417826773339196438857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12345890435697785595251809 9259417826773339196438857)
    ·
      refine ⟨6944563370080004397329143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9259417826773339196438857 6944563370080004397329143)
      ·
        refine ⟨10416845055120006595993715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944563370080004397329143 10416845055120006595993715)
        ·
          refine ⟨15625267582680009893990573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416845055120006595993715 15625267582680009893990573)
          ·
            refine ⟨5859475343505003710246465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15625267582680009893990573 5859475343505003710246465)
            ·
              refine ⟨4394606507628752782684849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859475343505003710246465 4394606507628752782684849)
              ·
                refine ⟨3295954880721564587013637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394606507628752782684849 3295954880721564587013637)
                ·
                  refine ⟨617991540135293360065057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3295954880721564587013637 617991540135293360065057)
                  ·
                    refine ⟨463493655101470020048793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617991540135293360065057 463493655101470020048793)
                    ·
                      refine ⟨347620241326102515036595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463493655101470020048793 347620241326102515036595)
                      ·
                        rfl

theorem cell23_676988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_676988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_676988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_676988 prefixEnd_676988 := by exact prefixLift 676988
  have htrace : WordTrace (prefixWord ++ tailWord_676988) baseStart_676988 baseEnd_676988 := by
    simpa [prefixWord, tailWord_676988, baseEnd_676988] using wordTrace_append hprefix tailTrace_676988
  have hstable : (prefixWord ++ tailWord_676988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_676988).length < 2 ^ (prefixWord ++ tailWord_676988).sum := by decide
  have hdescent : baseEnd_676988 < baseStart_676988 := by decide
  rcases family_descends (prefixWord ++ tailWord_676988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677011 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 5]
def baseStart_677011 : Nat := 118140960795 + 677011 * 2 ^ 59
def prefixEnd_677011 : Nat := 4983230072969 + 3 ^ 40 * 677011 * 2
def baseEnd_677011 : Nat := 38625783486795102783221

theorem tailTrace_677011 : CollatzResearch.WordTrace tailWord_677011 prefixEnd_677011 38625783486795102783221 := by
  unfold tailWord_677011
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692619750312246118590887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16461746500208164079060591 24692619750312246118590887)
  ·
    refine ⟨37038929625468369177886331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24692619750312246118590887 37038929625468369177886331)
    ·
      refine ⟨55558394438202553766829497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37038929625468369177886331 55558394438202553766829497)
      ·
        refine ⟨41668795828651915325122123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55558394438202553766829497 41668795828651915325122123)
        ·
          refine ⟨62503193742977872987683185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41668795828651915325122123 62503193742977872987683185)
          ·
            refine ⟨46877395307233404740762389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62503193742977872987683185 46877395307233404740762389)
            ·
              refine ⟨2197377905026565847223237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46877395307233404740762389 2197377905026565847223237)
              ·
                refine ⟨412008357192481096354357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2197377905026565847223237 412008357192481096354357)
                ·
                  refine ⟨38625783486795102783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412008357192481096354357 38625783486795102783221)
                  ·
                    rfl

theorem cell23_677011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 5].length) (baseStart_677011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677011 prefixEnd_677011 := by exact prefixLift 677011
  have htrace : WordTrace (prefixWord ++ tailWord_677011) baseStart_677011 baseEnd_677011 := by
    simpa [prefixWord, tailWord_677011, baseEnd_677011] using wordTrace_append hprefix tailTrace_677011
  have hstable : (prefixWord ++ tailWord_677011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677011).length < 2 ^ (prefixWord ++ tailWord_677011).sum := by decide
  have hdescent : baseEnd_677011 < baseStart_677011 := by decide
  rcases family_descends (prefixWord ++ tailWord_677011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677021 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_677021 : Nat := 118140960795 + 677021 * 2 ^ 59
def prefixEnd_677021 : Nat := 4983230072969 + 3 ^ 40 * 677021 * 2
def baseEnd_677021 : Nat := 347637186187700885923943

theorem tailTrace_677021 : CollatzResearch.WordTrace tailWord_677021 prefixEnd_677021 347637186187700885923943 := by
  unfold tailWord_677021
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692984480276017826454917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16461989653517345217636611 24692984480276017826454917)
  ·
    refine ⟨4629934590051753342460297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24692984480276017826454917 4629934590051753342460297)
    ·
      refine ⟨3472450942538815006845223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4629934590051753342460297 3472450942538815006845223)
      ·
        refine ⟨5208676413808222510267835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472450942538815006845223 5208676413808222510267835)
        ·
          refine ⟨7813014620712333765401753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208676413808222510267835 7813014620712333765401753)
          ·
            refine ⟨5859760965534250324051315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813014620712333765401753 5859760965534250324051315)
            ·
              refine ⟨8789641448301375486076973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859760965534250324051315 8789641448301375486076973)
              ·
                refine ⟨3296115543113015807278865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8789641448301375486076973 3296115543113015807278865)
                ·
                  refine ⟨2472086657334761855459149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296115543113015807278865 2472086657334761855459149)
                  ·
                    refine ⟨927032496500535695797181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472086657334761855459149 927032496500535695797181)
                    ·
                      refine ⟨347637186187700885923943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927032496500535695797181 347637186187700885923943)
                      ·
                        rfl

theorem cell23_677021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_677021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677021 prefixEnd_677021 := by exact prefixLift 677021
  have htrace : WordTrace (prefixWord ++ tailWord_677021) baseStart_677021 baseEnd_677021 := by
    simpa [prefixWord, tailWord_677021, baseEnd_677021] using wordTrace_append hprefix tailTrace_677021
  have hstable : (prefixWord ++ tailWord_677021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677021).length < 2 ^ (prefixWord ++ tailWord_677021).sum := by decide
  have hdescent : baseEnd_677021 < baseStart_677021 := by decide
  rcases family_descends (prefixWord ++ tailWord_677021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677022 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_677022 : Nat := 118140960795 + 677022 * 2 ^ 59
def prefixEnd_677022 : Nat := 4983230072969 + 3 ^ 40 * 677022 * 2
def baseEnd_677022 : Nat := 347637699668355382011439

theorem tailTrace_677022 : CollatzResearch.WordTrace tailWord_677022 prefixEnd_677022 347637699668355382011439 := by
  unfold tailWord_677022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086627619159049374655165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16462013968848263331494213 3086627619159049374655165)
  ·
    refine ⟨1157485357184643515495687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3086627619159049374655165 1157485357184643515495687)
    ·
      refine ⟨1736228035776965273243531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157485357184643515495687 1736228035776965273243531)
      ·
        refine ⟨2604342053665447909865297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736228035776965273243531 2604342053665447909865297)
        ·
          refine ⟨1953256540249085932398973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604342053665447909865297 1953256540249085932398973)
          ·
            refine ⟨732471202593407224649615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1953256540249085932398973 732471202593407224649615)
            ·
              refine ⟨1098706803890110836974423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732471202593407224649615 1098706803890110836974423)
              ·
                refine ⟨1648060205835166255461635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098706803890110836974423 1648060205835166255461635)
                ·
                  refine ⟨2472090308752749383192453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648060205835166255461635 2472090308752749383192453)
                  ·
                    refine ⟨463516932891140509348585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472090308752749383192453 463516932891140509348585)
                    ·
                      refine ⟨347637699668355382011439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463516932891140509348585 347637699668355382011439)
                      ·
                        rfl

theorem cell23_677022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_677022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677022 prefixEnd_677022 := by exact prefixLift 677022
  have htrace : WordTrace (prefixWord ++ tailWord_677022) baseStart_677022 baseEnd_677022 := by
    simpa [prefixWord, tailWord_677022, baseEnd_677022] using wordTrace_append hprefix tailTrace_677022
  have hstable : (prefixWord ++ tailWord_677022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677022).length < 2 ^ (prefixWord ++ tailWord_677022).sum := by decide
  have hdescent : baseEnd_677022 < baseStart_677022 := by decide
  rcases family_descends (prefixWord ++ tailWord_677022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677024 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_677024 : Nat := 118140960795 + 677024 * 2 ^ 59
def prefixEnd_677024 : Nat := 4983230072969 + 3 ^ 40 * 677024 * 2
def baseEnd_677024 : Nat := 115879575543221458062143

theorem tailTrace_677024 : CollatzResearch.WordTrace tailWord_677024 prefixEnd_677024 115879575543221458062143 := by
  unfold tailWord_677024
  simp only [CollatzResearch.WordTrace]
  refine ⟨12346546949632574669407063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16462062599510099559209417 12346546949632574669407063)
  ·
    refine ⟨18519820424448862004110595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12346546949632574669407063 18519820424448862004110595)
    ·
      refine ⟨27779730636673293006165893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18519820424448862004110595 27779730636673293006165893)
      ·
        refine ⟨5208699494376242438656105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27779730636673293006165893 5208699494376242438656105)
        ·
          refine ⟨3906524620782181828992079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5208699494376242438656105 3906524620782181828992079)
          ·
            refine ⟨5859786931173272743488119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906524620782181828992079 5859786931173272743488119)
            ·
              refine ⟨8789680396759909115232179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859786931173272743488119 8789680396759909115232179)
              ·
                refine ⟨13184520595139863672848269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789680396759909115232179 13184520595139863672848269)
                ·
                  refine ⟨4944195223177448877318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13184520595139863672848269 4944195223177448877318101)
                  ·
                    refine ⟨115879575543221458062143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4944195223177448877318101 115879575543221458062143)
                    ·
                      rfl

theorem cell23_677024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_677024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677024 prefixEnd_677024 := by exact prefixLift 677024
  have htrace : WordTrace (prefixWord ++ tailWord_677024) baseStart_677024 baseEnd_677024 := by
    simpa [prefixWord, tailWord_677024, baseEnd_677024] using wordTrace_append hprefix tailTrace_677024
  have hstable : (prefixWord ++ tailWord_677024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677024).length < 2 ^ (prefixWord ++ tailWord_677024).sum := by decide
  have hdescent : baseEnd_677024 < baseStart_677024 := by decide
  rcases family_descends (prefixWord ++ tailWord_677024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677041 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_677041 : Nat := 118140960795 + 677041 * 2 ^ 59
def prefixEnd_677041 : Nat := 4983230072969 + 3 ^ 40 * 677041 * 2
def baseEnd_677041 : Nat := 115882485266930269224617

theorem tailTrace_677041 : CollatzResearch.WordTrace tailWord_677041 prefixEnd_677041 115882485266930269224617 := by
  unfold tailWord_677041
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693713940203561242182977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16462475960135707494788651 24693713940203561242182977)
  ·
    refine ⟨18520285455152670931637233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24693713940203561242182977 18520285455152670931637233)
    ·
      refine ⟨13890214091364503198727925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18520285455152670931637233 13890214091364503198727925)
      ·
        refine ⟨1302207571065422174880743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13890214091364503198727925 1302207571065422174880743)
        ·
          refine ⟨1953311356598133262321115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302207571065422174880743 1953311356598133262321115)
          ·
            refine ⟨2929967034897199893481673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953311356598133262321115 2929967034897199893481673)
            ·
              refine ⟨2197475276172899920111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929967034897199893481673 2197475276172899920111255)
              ·
                refine ⟨3296212914259349880166883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197475276172899920111255 3296212914259349880166883)
                ·
                  refine ⟨4944319371389024820250325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296212914259349880166883 4944319371389024820250325)
                  ·
                    refine ⟨115882485266930269224617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4944319371389024820250325 115882485266930269224617)
                    ·
                      rfl

theorem cell23_677041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_677041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677041 prefixEnd_677041 := by exact prefixLift 677041
  have htrace : WordTrace (prefixWord ++ tailWord_677041) baseStart_677041 baseEnd_677041 := by
    simpa [prefixWord, tailWord_677041, baseEnd_677041] using wordTrace_append hprefix tailTrace_677041
  have hstable : (prefixWord ++ tailWord_677041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677041).length < 2 ^ (prefixWord ++ tailWord_677041).sum := by decide
  have hdescent : baseEnd_677041 < baseStart_677041 := by decide
  rcases family_descends (prefixWord ++ tailWord_677041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677071 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 3, 4]
def baseStart_677071 : Nat := 118140960795 + 677071 * 2 ^ 59
def prefixEnd_677071 : Nat := 4983230072969 + 3 ^ 40 * 677071 * 2
def baseEnd_677071 : Nat := 115887620073475230099571

theorem tailTrace_677071 : CollatzResearch.WordTrace tailWord_677071 prefixEnd_677071 115887620073475230099571 := by
  unfold tailWord_677071
  simp only [CollatzResearch.WordTrace]
  refine ⟨24694808130094876365775067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16463205420063250910516711 24694808130094876365775067)
  ·
    refine ⟨37042212195142314548662601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24694808130094876365775067 37042212195142314548662601)
    ·
      refine ⟨27781659146356735911496951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37042212195142314548662601 27781659146356735911496951)
      ·
        refine ⟨41672488719535103867245427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27781659146356735911496951 41672488719535103867245427)
        ·
          refine ⟨62508733079302655800868141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41672488719535103867245427 62508733079302655800868141)
          ·
            refine ⟨23440774904738495925325553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62508733079302655800868141 23440774904738495925325553)
            ·
              refine ⟨17580581178553871943994165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23440774904738495925325553 17580581178553871943994165)
              ·
                refine ⟨1648179485489425494749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17580581178553871943994165 1648179485489425494749453)
                ·
                  refine ⟨618067307058534560531045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1648179485489425494749453 618067307058534560531045)
                  ·
                    refine ⟨115887620073475230099571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618067307058534560531045 115887620073475230099571)
                    ·
                      rfl

theorem cell23_677071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_677071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677071 prefixEnd_677071 := by exact prefixLift 677071
  have htrace : WordTrace (prefixWord ++ tailWord_677071) baseStart_677071 baseEnd_677071 := by
    simpa [prefixWord, tailWord_677071, baseEnd_677071] using wordTrace_append hprefix tailTrace_677071
  have hstable : (prefixWord ++ tailWord_677071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677071).length < 2 ^ (prefixWord ++ tailWord_677071).sum := by decide
  have hdescent : baseEnd_677071 < baseStart_677071 := by decide
  rcases family_descends (prefixWord ++ tailWord_677071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677081 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_677081 : Nat := 118140960795 + 677081 * 2 ^ 59
def prefixEnd_677081 : Nat := 4983230072969 + 3 ^ 40 * 677081 * 2
def baseEnd_677081 : Nat := 347667995026970651173667

theorem tailTrace_677081 : CollatzResearch.WordTrace tailWord_677081 prefixEnd_677081 347667995026970651173667 := by
  unfold tailWord_677081
  simp only [CollatzResearch.WordTrace]
  refine ⟨24695172860058648073639097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16463448573372432049092731 24695172860058648073639097)
  ·
    refine ⟨18521379645043986055229323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24695172860058648073639097 18521379645043986055229323)
    ·
      refine ⟨27782069467565979082843985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18521379645043986055229323 27782069467565979082843985)
      ·
        refine ⟨20836552100674484312132989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27782069467565979082843985 20836552100674484312132989)
        ·
          refine ⟨7813707037752931617049871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20836552100674484312132989 7813707037752931617049871)
          ·
            refine ⟨11720560556629397425574807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813707037752931617049871 11720560556629397425574807)
            ·
              refine ⟨17580840834944096138362211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720560556629397425574807 17580840834944096138362211)
              ·
                refine ⟨26371261252416144207543317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17580840834944096138362211 26371261252416144207543317)
                ·
                  refine ⟨1236152871207006759728593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26371261252416144207543317 1236152871207006759728593)
                  ·
                    refine ⟨927114653405255069796445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236152871207006759728593 927114653405255069796445)
                    ·
                      refine ⟨347667995026970651173667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927114653405255069796445 347667995026970651173667)
                      ·
                        rfl

theorem cell23_677081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_677081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677081 prefixEnd_677081 := by exact prefixLift 677081
  have htrace : WordTrace (prefixWord ++ tailWord_677081) baseStart_677081 baseEnd_677081 := by
    simpa [prefixWord, tailWord_677081, baseEnd_677081] using wordTrace_append hprefix tailTrace_677081
  have hstable : (prefixWord ++ tailWord_677081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677081).length < 2 ^ (prefixWord ++ tailWord_677081).sum := by decide
  have hdescent : baseEnd_677081 < baseStart_677081 := by decide
  rcases family_descends (prefixWord ++ tailWord_677081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677095 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_677095 : Nat := 118140960795 + 677095 * 2 ^ 59
def prefixEnd_677095 : Nat := 4983230072969 + 3 ^ 40 * 677095 * 2
def baseEnd_677095 : Nat := 347675183756133596398603

theorem tailTrace_677095 : CollatzResearch.WordTrace tailWord_677095 prefixEnd_677095 347675183756133596398603 := by
  unfold tailWord_677095
  simp only [CollatzResearch.WordTrace]
  refine ⟨24695683482007928464648739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16463788988005285643099159 24695683482007928464648739)
  ·
    refine ⟨37043525223011892696973109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24695683482007928464648739 37043525223011892696973109)
    ·
      refine ⟨3472830489657364940341229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37043525223011892696973109 3472830489657364940341229)
      ·
        refine ⟨1302311433621511852627961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3472830489657364940341229 1302311433621511852627961)
        ·
          refine ⟨976733575216133889470971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302311433621511852627961 976733575216133889470971)
          ·
            refine ⟨1465100362824200834206457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976733575216133889470971 1465100362824200834206457)
            ·
              refine ⟨1098825272118150625654843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465100362824200834206457 1098825272118150625654843)
              ·
                refine ⟨1648237908177225938482265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098825272118150625654843 1648237908177225938482265)
                ·
                  refine ⟨1236178431132919453861699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648237908177225938482265 1236178431132919453861699)
                  ·
                    refine ⟨1854267646699379180792549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1236178431132919453861699 1854267646699379180792549)
                    ·
                      refine ⟨347675183756133596398603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1854267646699379180792549 347675183756133596398603)
                      ·
                        rfl

theorem cell23_677095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_677095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677095 prefixEnd_677095 := by exact prefixLift 677095
  have htrace : WordTrace (prefixWord ++ tailWord_677095) baseStart_677095 baseEnd_677095 := by
    simpa [prefixWord, tailWord_677095, baseEnd_677095] using wordTrace_append hprefix tailTrace_677095
  have hstable : (prefixWord ++ tailWord_677095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677095).length < 2 ^ (prefixWord ++ tailWord_677095).sum := by decide
  have hdescent : baseEnd_677095 < baseStart_677095 := by decide
  rcases family_descends (prefixWord ++ tailWord_677095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677098 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_677098 : Nat := 118140960795 + 677098 * 2 ^ 59
def prefixEnd_677098 : Nat := 4983230072969 + 3 ^ 40 * 677098 * 2
def baseEnd_677098 : Nat := 347676724198097084661089

theorem tailTrace_677098 : CollatzResearch.WordTrace tailWord_677098 prefixEnd_677098 347676724198097084661089 := by
  unfold tailWord_677098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6173948225249264994251987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16463861933998039984671965 6173948225249264994251987)
  ·
    refine ⟨9260922337873897491377981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6173948225249264994251987 9260922337873897491377981)
    ·
      refine ⟨3472845876702711559266743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9260922337873897491377981 3472845876702711559266743)
      ·
        refine ⟨5209268815054067338900115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472845876702711559266743 5209268815054067338900115)
        ·
          refine ⟨7813903222581101008350173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209268815054067338900115 7813903222581101008350173)
          ·
            refine ⟨2930213708467912878131315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7813903222581101008350173 2930213708467912878131315)
            ·
              refine ⟨4395320562701869317196973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930213708467912878131315 4395320562701869317196973)
              ·
                refine ⟨1648245211013200993948865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4395320562701869317196973 1648245211013200993948865)
                ·
                  refine ⟨1236183908259900745461649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648245211013200993948865 1236183908259900745461649)
                  ·
                    refine ⟨927137931194925559096237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236183908259900745461649 927137931194925559096237)
                    ·
                      refine ⟨347676724198097084661089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927137931194925559096237 347676724198097084661089)
                      ·
                        rfl

theorem cell23_677098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_677098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677098 prefixEnd_677098 := by exact prefixLift 677098
  have htrace : WordTrace (prefixWord ++ tailWord_677098) baseStart_677098 baseEnd_677098 := by
    simpa [prefixWord, tailWord_677098, baseEnd_677098] using wordTrace_append hprefix tailTrace_677098
  have hstable : (prefixWord ++ tailWord_677098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677098).length < 2 ^ (prefixWord ++ tailWord_677098).sum := by decide
  have hdescent : baseEnd_677098 < baseStart_677098 := by decide
  rcases family_descends (prefixWord ++ tailWord_677098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677104 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_677104 : Nat := 118140960795 + 677104 * 2 ^ 59
def prefixEnd_677104 : Nat := 4983230072969 + 3 ^ 40 * 677104 * 2
def baseEnd_677104 : Nat := 347679805082024061186061

theorem tailTrace_677104 : CollatzResearch.WordTrace tailWord_677104 prefixEnd_677104 347679805082024061186061 := by
  unfold tailWord_677104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12348005869487661500863183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16464007825983548667817577 12348005869487661500863183)
  ·
    refine ⟨18522008804231492251294775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12348005869487661500863183 18522008804231492251294775)
    ·
      refine ⟨27783013206347238376942163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522008804231492251294775 27783013206347238376942163)
      ·
        refine ⟨41674519809520857565413245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27783013206347238376942163 41674519809520857565413245)
        ·
          refine ⟨15627944928570321587029967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41674519809520857565413245 15627944928570321587029967)
          ·
            refine ⟨23441917392855482380544951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15627944928570321587029967 23441917392855482380544951)
            ·
              refine ⟨35162876089283223570817427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23441917392855482380544951 35162876089283223570817427)
              ·
                refine ⟨52744314133924835356226141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35162876089283223570817427 52744314133924835356226141)
                ·
                  refine ⟨19779117800221813258584803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52744314133924835356226141 19779117800221813258584803)
                  ·
                    refine ⟨29668676700332719887877205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19779117800221813258584803 29668676700332719887877205)
                    ·
                      refine ⟨347679805082024061186061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 29668676700332719887877205 347679805082024061186061)
                      ·
                        rfl

theorem cell23_677104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_677104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677104 prefixEnd_677104 := by exact prefixLift 677104
  have htrace : WordTrace (prefixWord ++ tailWord_677104) baseStart_677104 baseEnd_677104 := by
    simpa [prefixWord, tailWord_677104, baseEnd_677104] using wordTrace_append hprefix tailTrace_677104
  have hstable : (prefixWord ++ tailWord_677104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677104).length < 2 ^ (prefixWord ++ tailWord_677104).sum := by decide
  have hdescent : baseEnd_677104 < baseStart_677104 := by decide
  rcases family_descends (prefixWord ++ tailWord_677104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677118 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_677118 : Nat := 118140960795 + 677118 * 2 ^ 59
def prefixEnd_677118 : Nat := 4983230072969 + 3 ^ 40 * 677118 * 2
def baseEnd_677118 : Nat := 38631888201243000712333

theorem tailTrace_677118 : CollatzResearch.WordTrace tailWord_677118 prefixEnd_677118 38631888201243000712333 := by
  unfold tailWord_677118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087065295115575424092001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16464348240616402261824005 3087065295115575424092001)
  ·
    refine ⟨2315298971336681568069001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3087065295115575424092001 2315298971336681568069001)
    ·
      refine ⟨1736474228502511176051751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2315298971336681568069001 1736474228502511176051751)
      ·
        refine ⟨2604711342753766764077627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736474228502511176051751 2604711342753766764077627)
        ·
          refine ⟨3907067014130650146116441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604711342753766764077627 3907067014130650146116441)
          ·
            refine ⟨2930300260597987609587331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907067014130650146116441 2930300260597987609587331)
            ·
              refine ⟨4395450390896981414380997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930300260597987609587331 4395450390896981414380997)
              ·
                refine ⟨824146948293184015196437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4395450390896981414380997 824146948293184015196437)
                ·
                  refine ⟨38631888201243000712333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 824146948293184015196437 38631888201243000712333)
                  ·
                    rfl

theorem cell23_677118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_677118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677118 prefixEnd_677118 := by exact prefixLift 677118
  have htrace : WordTrace (prefixWord ++ tailWord_677118) baseStart_677118 baseEnd_677118 := by
    simpa [prefixWord, tailWord_677118, baseEnd_677118] using wordTrace_append hprefix tailTrace_677118
  have hstable : (prefixWord ++ tailWord_677118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677118).length < 2 ^ (prefixWord ++ tailWord_677118).sum := by decide
  have hdescent : baseEnd_677118 < baseStart_677118 := by decide
  rcases family_descends (prefixWord ++ tailWord_677118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677131 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 3, 5]
def baseStart_677131 : Nat := 118140960795 + 677131 * 2 ^ 59
def prefixEnd_677131 : Nat := 4983230072969 + 3 ^ 40 * 677131 * 2
def baseEnd_677131 : Nat := 115897889686565151849479

theorem tailTrace_677131 : CollatzResearch.WordTrace tailWord_677131 prefixEnd_677131 115897889686565151849479 := by
  unfold tailWord_677131
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696996509877506612959247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16464664339918337741972831 24696996509877506612959247)
  ·
    refine ⟨37045494764816259919438871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24696996509877506612959247 37045494764816259919438871)
    ·
      refine ⟨55568242147224389879158307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37045494764816259919438871 55568242147224389879158307)
      ·
        refine ⟨83352363220836584818737461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55568242147224389879158307 83352363220836584818737461)
        ·
          refine ⟨7814284051953429826756637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83352363220836584818737461 7814284051953429826756637)
          ·
            refine ⟨2930356519482536185033739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7814284051953429826756637 2930356519482536185033739)
            ·
              refine ⟨4395534779223804277550609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930356519482536185033739 4395534779223804277550609)
              ·
                refine ⟨3296651084417853208162957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395534779223804277550609 3296651084417853208162957)
                ·
                  refine ⟨1236244156656694953061109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3296651084417853208162957 1236244156656694953061109)
                  ·
                    refine ⟨115897889686565151849479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1236244156656694953061109 115897889686565151849479)
                    ·
                      rfl

theorem cell23_677131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 5].length) (baseStart_677131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677131 prefixEnd_677131 := by exact prefixLift 677131
  have htrace : WordTrace (prefixWord ++ tailWord_677131) baseStart_677131 baseEnd_677131 := by
    simpa [prefixWord, tailWord_677131, baseEnd_677131] using wordTrace_append hprefix tailTrace_677131
  have hstable : (prefixWord ++ tailWord_677131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677131).length < 2 ^ (prefixWord ++ tailWord_677131).sum := by decide
  have hdescent : baseEnd_677131 < baseStart_677131 := by decide
  rcases family_descends (prefixWord ++ tailWord_677131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677155 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 2, 3, 2]
def baseStart_677155 : Nat := 118140960795 + 677155 * 2 ^ 59
def prefixEnd_677155 : Nat := 4983230072969 + 3 ^ 40 * 677155 * 2
def baseEnd_677155 : Nat := 347705992595403361648327

theorem tailTrace_677155 : CollatzResearch.WordTrace tailWord_677155 prefixEnd_677155 347705992595403361648327 := by
  unfold tailWord_677155
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697871861790558711832919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16465247907860372474555279 24697871861790558711832919)
  ·
    refine ⟨37046807792685838067749379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24697871861790558711832919 37046807792685838067749379)
    ·
      refine ⟨55570211689028757101624069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37046807792685838067749379 55570211689028757101624069)
      ·
        refine ⟨10419414691692891956554513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55570211689028757101624069 10419414691692891956554513)
        ·
          refine ⟨7814561018769668967415885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10419414691692891956554513 7814561018769668967415885)
          ·
            refine ⟨2930460382038625862780957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7814561018769668967415885 2930460382038625862780957)
            ·
              refine ⟨1098922643264484698542859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2930460382038625862780957 1098922643264484698542859)
              ·
                refine ⟨1648383964896727047814289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098922643264484698542859 1648383964896727047814289)
                ·
                  refine ⟨1236287973672545285860717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648383964896727047814289 1236287973672545285860717)
                  ·
                    refine ⟨463607990127204482197769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236287973672545285860717 463607990127204482197769)
                    ·
                      refine ⟨347705992595403361648327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463607990127204482197769 347705992595403361648327)
                      ·
                        rfl

theorem cell23_677155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_677155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677155 prefixEnd_677155 := by exact prefixLift 677155
  have htrace : WordTrace (prefixWord ++ tailWord_677155) baseStart_677155 baseEnd_677155 := by
    simpa [prefixWord, tailWord_677155, baseEnd_677155] using wordTrace_append hprefix tailTrace_677155
  have hstable : (prefixWord ++ tailWord_677155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677155).length < 2 ^ (prefixWord ++ tailWord_677155).sum := by decide
  have hdescent : baseEnd_677155 < baseStart_677155 := by decide
  rcases family_descends (prefixWord ++ tailWord_677155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677168 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_677168 : Nat := 118140960795 + 677168 * 2 ^ 59
def prefixEnd_677168 : Nat := 4983230072969 + 3 ^ 40 * 677168 * 2
def baseEnd_677168 : Nat := 347712667843911810785767

theorem tailTrace_677168 : CollatzResearch.WordTrace tailWord_677168 prefixEnd_677168 347712667843911810785767 := by
  unfold tailWord_677168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349173005371730966028079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16465564007162307954704105 12349173005371730966028079)
  ·
    refine ⟨18523759508057596449042119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12349173005371730966028079 18523759508057596449042119)
    ·
      refine ⟨27785639262086394673563179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18523759508057596449042119 27785639262086394673563179)
      ·
        refine ⟨41678458893129592010344769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27785639262086394673563179 41678458893129592010344769)
        ·
          refine ⟨31258844169847194007758577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41678458893129592010344769 31258844169847194007758577)
          ·
            refine ⟨23444133127385395505818933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31258844169847194007758577 23444133127385395505818933)
            ·
              refine ⟨2197887480692380828670525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23444133127385395505818933 2197887480692380828670525)
              ·
                refine ⟨824207805259642810751447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197887480692380828670525 824207805259642810751447)
                ·
                  refine ⟨1236311707889464216127171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824207805259642810751447 1236311707889464216127171)
                  ·
                    refine ⟨1854467561834196324190757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1236311707889464216127171 1854467561834196324190757)
                    ·
                      refine ⟨347712667843911810785767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1854467561834196324190757 347712667843911810785767)
                      ·
                        rfl

theorem cell23_677168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_677168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677168 prefixEnd_677168 := by exact prefixLift 677168
  have htrace : WordTrace (prefixWord ++ tailWord_677168) baseStart_677168 baseEnd_677168 := by
    simpa [prefixWord, tailWord_677168, baseEnd_677168] using wordTrace_append hprefix tailTrace_677168
  have hstable : (prefixWord ++ tailWord_677168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677168).length < 2 ^ (prefixWord ++ tailWord_677168).sum := by decide
  have hdescent : baseEnd_677168 < baseStart_677168 := by decide
  rcases family_descends (prefixWord ++ tailWord_677168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677178 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_677178 : Nat := 118140960795 + 677178 * 2 ^ 59
def prefixEnd_677178 : Nat := 4983230072969 + 3 ^ 40 * 677178 * 2
def baseEnd_677178 : Nat := 115905934216818923886907

theorem tailTrace_677178 : CollatzResearch.WordTrace tailWord_677178 prefixEnd_677178 115905934216818923886907 := by
  unfold tailWord_677178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174677685176808409980047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16465807160471489093280125 6174677685176808409980047)
  ·
    refine ⟨9262016527765212614970071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174677685176808409980047 9262016527765212614970071)
    ·
      refine ⟨13893024791647818922455107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262016527765212614970071 13893024791647818922455107)
      ·
        refine ⟨20839537187471728383682661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13893024791647818922455107 20839537187471728383682661)
        ·
          refine ⟨3907413222650949071940499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20839537187471728383682661 3907413222650949071940499)
          ·
            refine ⟨5861119833976423607910749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907413222650949071940499 5861119833976423607910749)
            ·
              refine ⟨2197919937741158852966531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5861119833976423607910749 2197919937741158852966531)
              ·
                refine ⟨3296879906611738279449797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197919937741158852966531 3296879906611738279449797)
                ·
                  refine ⟨618164982489700927396837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3296879906611738279449797 618164982489700927396837)
                  ·
                    refine ⟨115905934216818923886907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618164982489700927396837 115905934216818923886907)
                    ·
                      rfl

theorem cell23_677178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_677178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677178 prefixEnd_677178 := by exact prefixLift 677178
  have htrace : WordTrace (prefixWord ++ tailWord_677178) baseStart_677178 baseEnd_677178 := by
    simpa [prefixWord, tailWord_677178, baseEnd_677178] using wordTrace_append hprefix tailTrace_677178
  have hstable : (prefixWord ++ tailWord_677178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677178).length < 2 ^ (prefixWord ++ tailWord_677178).sum := by decide
  have hdescent : baseEnd_677178 < baseStart_677178 := by decide
  rcases family_descends (prefixWord ++ tailWord_677178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677205 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_677205 : Nat := 118140960795 + 677205 * 2 ^ 59
def prefixEnd_677205 : Nat := 4983230072969 + 3 ^ 40 * 677205 * 2
def baseEnd_677205 : Nat := 347731666628128166023097

theorem tailTrace_677205 : CollatzResearch.WordTrace tailWord_677205 prefixEnd_677205 347731666628128166023097 := by
  unfold tailWord_677205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24699695511609417251153069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16466463674406278167435379 24699695511609417251153069)
  ·
    refine ⟨9262385816853531469182401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24699695511609417251153069 9262385816853531469182401)
    ·
      refine ⟨6946789362640148601886801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9262385816853531469182401 6946789362640148601886801)
      ·
        refine ⟨5210092021980111451415101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6946789362640148601886801 5210092021980111451415101)
        ·
          refine ⟨1953784508242541794280663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5210092021980111451415101 1953784508242541794280663)
          ·
            refine ⟨2930676762363812691420995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953784508242541794280663 2930676762363812691420995)
            ·
              refine ⟨4396015143545719037131493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930676762363812691420995 4396015143545719037131493)
              ·
                refine ⟨824252839414822319462155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396015143545719037131493 824252839414822319462155)
                ·
                  refine ⟨1236379259122233479193233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824252839414822319462155 1236379259122233479193233)
                  ·
                    refine ⟨927284444341675109394925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236379259122233479193233 927284444341675109394925)
                    ·
                      refine ⟨347731666628128166023097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927284444341675109394925 347731666628128166023097)
                      ·
                        rfl

theorem cell23_677205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_677205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677205 prefixEnd_677205 := by exact prefixLift 677205
  have htrace : WordTrace (prefixWord ++ tailWord_677205) baseStart_677205 baseEnd_677205 := by
    simpa [prefixWord, tailWord_677205, baseEnd_677205] using wordTrace_append hprefix tailTrace_677205
  have hstable : (prefixWord ++ tailWord_677205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677205).length < 2 ^ (prefixWord ++ tailWord_677205).sum := by decide
  have hdescent : baseEnd_677205 < baseStart_677205 := by decide
  rcases family_descends (prefixWord ++ tailWord_677205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677219 : List Nat := [1, 1, 1, 5, 2, 2, 3, 3, 1, 2, 2]
def baseStart_677219 : Nat := 118140960795 + 677219 * 2 ^ 59
def prefixEnd_677219 : Nat := 4983230072969 + 3 ^ 40 * 677219 * 2
def baseEnd_677219 : Nat := 347738855357291111248033

theorem tailTrace_677219 : CollatzResearch.WordTrace tailWord_677219 prefixEnd_677219 347738855357291111248033 := by
  unfold tailWord_677219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700206133558697642162711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16466804089039131761441807 24700206133558697642162711)
  ·
    refine ⟨37050309200338046463244067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24700206133558697642162711 37050309200338046463244067)
    ·
      refine ⟨55575463800507069694866101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37050309200338046463244067 55575463800507069694866101)
      ·
        refine ⟨5210199731297537783893697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55575463800507069694866101 5210199731297537783893697)
        ·
          refine ⟨3907649798473153337920273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5210199731297537783893697 3907649798473153337920273)
          ·
            refine ⟨2930737348854865003440205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907649798473153337920273 2930737348854865003440205)
            ·
              refine ⟨1099026505820574376290077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2930737348854865003440205 1099026505820574376290077)
              ·
                refine ⟨412134939682715391108779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099026505820574376290077 412134939682715391108779)
                ·
                  refine ⟨618202409524073086663169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412134939682715391108779 618202409524073086663169)
                  ·
                    refine ⟨463651807143054814997377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618202409524073086663169 463651807143054814997377)
                    ·
                      refine ⟨347738855357291111248033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463651807143054814997377 347738855357291111248033)
                      ·
                        rfl

theorem cell23_677219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_677219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677219 prefixEnd_677219 := by exact prefixLift 677219
  have htrace : WordTrace (prefixWord ++ tailWord_677219) baseStart_677219 baseEnd_677219 := by
    simpa [prefixWord, tailWord_677219, baseEnd_677219] using wordTrace_append hprefix tailTrace_677219
  have hstable : (prefixWord ++ tailWord_677219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677219).length < 2 ^ (prefixWord ++ tailWord_677219).sum := by decide
  have hdescent : baseEnd_677219 < baseStart_677219 := by decide
  rcases family_descends (prefixWord ++ tailWord_677219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677231 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_677231 : Nat := 118140960795 + 677231 * 2 ^ 59
def prefixEnd_677231 : Nat := 4983230072969 + 3 ^ 40 * 677231 * 2
def baseEnd_677231 : Nat := 347745017125145064297977

theorem tailTrace_677231 : CollatzResearch.WordTrace tailWord_677231 prefixEnd_677231 347745017125145064297977 := by
  unfold tailWord_677231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700643809515223691599547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467095873010149127733031 24700643809515223691599547)
  ·
    refine ⟨37050965714272835537399321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24700643809515223691599547 37050965714272835537399321)
    ·
      refine ⟨27788224285704626653049491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37050965714272835537399321 27788224285704626653049491)
      ·
        refine ⟨41682336428556939979574237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27788224285704626653049491 41682336428556939979574237)
        ·
          refine ⟨15630876160708852492340339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41682336428556939979574237 15630876160708852492340339)
          ·
            refine ⟨23446314241063278738510509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630876160708852492340339 23446314241063278738510509)
            ·
              refine ⟨8792367840398729526941441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23446314241063278738510509 8792367840398729526941441)
              ·
                refine ⟨6594275880299047145206081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792367840398729526941441 6594275880299047145206081)
                ·
                  refine ⟨4945706910224285358904561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6594275880299047145206081 4945706910224285358904561)
                  ·
                    refine ⟨3709280182668214019178421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945706910224285358904561 3709280182668214019178421)
                    ·
                      refine ⟨347745017125145064297977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3709280182668214019178421 347745017125145064297977)
                      ·
                        rfl

theorem cell23_677231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_677231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677231 prefixEnd_677231 := by exact prefixLift 677231
  have htrace : WordTrace (prefixWord ++ tailWord_677231) baseStart_677231 baseEnd_677231 := by
    simpa [prefixWord, tailWord_677231, baseEnd_677231] using wordTrace_append hprefix tailTrace_677231
  have hstable : (prefixWord ++ tailWord_677231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677231).length < 2 ^ (prefixWord ++ tailWord_677231).sum := by decide
  have hdescent : baseEnd_677231 < baseStart_677231 := by decide
  rcases family_descends (prefixWord ++ tailWord_677231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677245 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_677245 : Nat := 118140960795 + 677245 * 2 ^ 59
def prefixEnd_677245 : Nat := 4983230072969 + 3 ^ 40 * 677245 * 2
def baseEnd_677245 : Nat := 347752205854308009522913

theorem tailTrace_677245 : CollatzResearch.WordTrace tailWord_677245 prefixEnd_677245 347752205854308009522913 := by
  unfold tailWord_677245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24701154431464504082609189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16467436287643002721739459 24701154431464504082609189)
  ·
    refine ⟨4631466455899594515489223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24701154431464504082609189 4631466455899594515489223)
    ·
      refine ⟨6947199683849391773233835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4631466455899594515489223 6947199683849391773233835)
      ·
        refine ⟨10420799525774087659850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947199683849391773233835 10420799525774087659850753)
        ·
          refine ⟨7815599644330565744888065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10420799525774087659850753 7815599644330565744888065)
          ·
            refine ⟨5861699733247924308666049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7815599644330565744888065 5861699733247924308666049)
            ·
              refine ⟨4396274799935943231499537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861699733247924308666049 4396274799935943231499537)
              ·
                refine ⟨3297206099951957423624653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396274799935943231499537 3297206099951957423624653)
                ·
                  refine ⟨1236452287481984033859245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3297206099951957423624653 1236452287481984033859245)
                  ·
                    refine ⟨463669607805744012697217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236452287481984033859245 463669607805744012697217)
                    ·
                      refine ⟨347752205854308009522913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463669607805744012697217 347752205854308009522913)
                      ·
                        rfl

theorem cell23_677245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_677245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677245 prefixEnd_677245 := by exact prefixLift 677245
  have htrace : WordTrace (prefixWord ++ tailWord_677245) baseStart_677245 baseEnd_677245 := by
    simpa [prefixWord, tailWord_677245, baseEnd_677245] using wordTrace_append hprefix tailTrace_677245
  have hstable : (prefixWord ++ tailWord_677245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677245).length < 2 ^ (prefixWord ++ tailWord_677245).sum := by decide
  have hdescent : baseEnd_677245 < baseStart_677245 := by decide
  rcases family_descends (prefixWord ++ tailWord_677245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677252 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_677252 : Nat := 118140960795 + 677252 * 2 ^ 59
def prefixEnd_677252 : Nat := 4983230072969 + 3 ^ 40 * 677252 * 2
def baseEnd_677252 : Nat := 347755800218889482135381

theorem tailTrace_677252 : CollatzResearch.WordTrace tailWord_677252 prefixEnd_677252 347755800218889482135381 := by
  unfold tailWord_677252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350704871219572139057005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16467606494959429518742673 12350704871219572139057005)
  ·
    refine ⟨4631514326707339552146377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12350704871219572139057005 4631514326707339552146377)
    ·
      refine ⟨3473635745030504664109783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4631514326707339552146377 3473635745030504664109783)
      ·
        refine ⟨5210453617545756996164675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473635745030504664109783 5210453617545756996164675)
        ·
          refine ⟨7815680426318635494247013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210453617545756996164675 7815680426318635494247013)
          ·
            refine ⟨1465440079934744155171315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7815680426318635494247013 1465440079934744155171315)
            ·
              refine ⟨2198160119902116232756973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465440079934744155171315 2198160119902116232756973)
              ·
                refine ⟨824310044963293587283865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198160119902116232756973 824310044963293587283865)
                ·
                  refine ⟨618232533722470190462899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824310044963293587283865 618232533722470190462899)
                  ·
                    refine ⟨927348800583705285694349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 618232533722470190462899 927348800583705285694349)
                    ·
                      refine ⟨347755800218889482135381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927348800583705285694349 347755800218889482135381)
                      ·
                        rfl

theorem cell23_677252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_677252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677252 prefixEnd_677252 := by exact prefixLift 677252
  have htrace : WordTrace (prefixWord ++ tailWord_677252) baseStart_677252 baseEnd_677252 := by
    simpa [prefixWord, tailWord_677252, baseEnd_677252] using wordTrace_append hprefix tailTrace_677252
  have hstable : (prefixWord ++ tailWord_677252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677252).length < 2 ^ (prefixWord ++ tailWord_677252).sum := by decide
  have hdescent : baseEnd_677252 < baseStart_677252 := by decide
  rcases family_descends (prefixWord ++ tailWord_677252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677279 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 1, 3, 2]
def baseStart_677279 : Nat := 118140960795 + 677279 * 2 ^ 59
def prefixEnd_677279 : Nat := 4983230072969 + 3 ^ 40 * 677279 * 2
def baseEnd_677279 : Nat := 347769664196560876497757

theorem tailTrace_677279 : CollatzResearch.WordTrace tailWord_677279 prefixEnd_677279 347769664196560876497757 := by
  unfold tailWord_677279
  simp only [CollatzResearch.WordTrace]
  refine ⟨24702394513341327889346891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16468263008894218592897927 24702394513341327889346891)
  ·
    refine ⟨37053591770011991834020337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24702394513341327889346891 37053591770011991834020337)
    ·
      refine ⟨27790193827508993875515253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37053591770011991834020337 27790193827508993875515253)
      ·
        refine ⟨2605330671328968175829555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27790193827508993875515253 2605330671328968175829555)
        ·
          refine ⟨3907996006993452263744333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605330671328968175829555 3907996006993452263744333)
          ·
            refine ⟨1465498502622544598904125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3907996006993452263744333 1465498502622544598904125)
            ·
              refine ⟨549561938483454224589047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1465498502622544598904125 549561938483454224589047)
              ·
                refine ⟨824342907725181336883571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549561938483454224589047 824342907725181336883571)
                ·
                  refine ⟨1236514361587772005325357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824342907725181336883571 1236514361587772005325357)
                  ·
                    refine ⟨463692885595414501997009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236514361587772005325357 463692885595414501997009)
                    ·
                      refine ⟨347769664196560876497757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463692885595414501997009 347769664196560876497757)
                      ·
                        rfl

theorem cell23_677279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_677279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677279 prefixEnd_677279 := by exact prefixLift 677279
  have htrace : WordTrace (prefixWord ++ tailWord_677279) baseStart_677279 baseEnd_677279 := by
    simpa [prefixWord, tailWord_677279, baseEnd_677279] using wordTrace_append hprefix tailTrace_677279
  have hstable : (prefixWord ++ tailWord_677279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677279).length < 2 ^ (prefixWord ++ tailWord_677279).sum := by decide
  have hdescent : baseEnd_677279 < baseStart_677279 := by decide
  rcases family_descends (prefixWord ++ tailWord_677279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677292 : List Nat := [2, 2, 1, 1, 1, 1, 5, 4, 2, 2, 2]
def baseStart_677292 : Nat := 118140960795 + 677292 * 2 ^ 59
def prefixEnd_677292 : Nat := 4983230072969 + 3 ^ 40 * 677292 * 2
def baseEnd_677292 : Nat := 347776339445069325635197

theorem tailTrace_677292 : CollatzResearch.WordTrace tailWord_677292 prefixEnd_677292 347776339445069325635197 := by
  unfold tailWord_677292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351434331147115554785065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16468579108196154073046753 12351434331147115554785065)
  ·
    refine ⟨9263575748360336666088799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12351434331147115554785065 9263575748360336666088799)
    ·
      refine ⟨13895363622540504999133199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9263575748360336666088799 13895363622540504999133199)
      ·
        refine ⟨20843045433810757498699799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13895363622540504999133199 20843045433810757498699799)
        ·
          refine ⟨31264568150716136248049699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20843045433810757498699799 31264568150716136248049699)
          ·
            refine ⟨46896852226074204372074549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31264568150716136248049699 46896852226074204372074549)
            ·
              refine ⟨4396579896194456659881989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46896852226074204372074549 4396579896194456659881989)
              ·
                refine ⟨824358730536460623727873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396579896194456659881989 824358730536460623727873)
                ·
                  refine ⟨618269047902345467795905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824358730536460623727873 618269047902345467795905)
                  ·
                    refine ⟨463701785926759100846929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618269047902345467795905 463701785926759100846929)
                    ·
                      refine ⟨347776339445069325635197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463701785926759100846929 347776339445069325635197)
                      ·
                        rfl

theorem cell23_677292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_677292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677292 prefixEnd_677292 := by exact prefixLift 677292
  have htrace : WordTrace (prefixWord ++ tailWord_677292) baseStart_677292 baseEnd_677292 := by
    simpa [prefixWord, tailWord_677292, baseEnd_677292] using wordTrace_append hprefix tailTrace_677292
  have hstable : (prefixWord ++ tailWord_677292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677292).length < 2 ^ (prefixWord ++ tailWord_677292).sum := by decide
  have hdescent : baseEnd_677292 < baseStart_677292 := by decide
  rcases family_descends (prefixWord ++ tailWord_677292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677305 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_677305 : Nat := 118140960795 + 677305 * 2 ^ 59
def prefixEnd_677305 : Nat := 4983230072969 + 3 ^ 40 * 677305 * 2
def baseEnd_677305 : Nat := 347783014693577774772637

theorem tailTrace_677305 : CollatzResearch.WordTrace tailWord_677305 prefixEnd_677305 347783014693577774772637 := by
  unfold tailWord_677305
  simp only [CollatzResearch.WordTrace]
  refine ⟨24703342811247134329793369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16468895207498089553195579 24703342811247134329793369)
  ·
    refine ⟨18527507108435350747345027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24703342811247134329793369 18527507108435350747345027)
    ·
      refine ⟨27791260662653026121017541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18527507108435350747345027 27791260662653026121017541)
      ·
        refine ⟨5210861374247442397690789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27791260662653026121017541 5210861374247442397690789)
        ·
          refine ⟨977036507671395449567023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5210861374247442397690789 977036507671395449567023)
          ·
            refine ⟨1465554761507093174350535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977036507671395449567023 1465554761507093174350535)
            ·
              refine ⟨2198332142260639761525803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465554761507093174350535 2198332142260639761525803)
              ·
                refine ⟨3297498213390959642288705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198332142260639761525803 3297498213390959642288705)
                ·
                  refine ⟨2473123660043219731716529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297498213390959642288705 2473123660043219731716529)
                  ·
                    refine ⟨1854842745032414798787397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2473123660043219731716529 1854842745032414798787397)
                    ·
                      refine ⟨347783014693577774772637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1854842745032414798787397 347783014693577774772637)
                      ·
                        rfl

theorem cell23_677305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_677305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677305 prefixEnd_677305 := by exact prefixLift 677305
  have htrace : WordTrace (prefixWord ++ tailWord_677305) baseStart_677305 baseEnd_677305 := by
    simpa [prefixWord, tailWord_677305, baseEnd_677305] using wordTrace_append hprefix tailTrace_677305
  have hstable : (prefixWord ++ tailWord_677305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677305).length < 2 ^ (prefixWord ++ tailWord_677305).sum := by decide
  have hdescent : baseEnd_677305 < baseStart_677305 := by decide
  rcases family_descends (prefixWord ++ tailWord_677305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677385 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_677385 : Nat := 118140960795 + 677385 * 2 ^ 59
def prefixEnd_677385 : Nat := 4983230072969 + 3 ^ 40 * 677385 * 2
def baseEnd_677385 : Nat := 347824093145937461772269

theorem tailTrace_677385 : CollatzResearch.WordTrace tailWord_677385 prefixEnd_677385 347824093145937461772269 := by
  unfold tailWord_677385
  simp only [CollatzResearch.WordTrace]
  refine ⟨24706260650957307992705609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16470840433971538661803739 24706260650957307992705609)
  ·
    refine ⟨18529695488217980994529207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24706260650957307992705609 18529695488217980994529207)
    ·
      refine ⟨27794543232326971491793811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18529695488217980994529207 27794543232326971491793811)
      ·
        refine ⟨41691814848490457237690717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27794543232326971491793811 41691814848490457237690717)
        ·
          refine ⟨15634430568183921464134019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41691814848490457237690717 15634430568183921464134019)
          ·
            refine ⟨23451645852275882196201029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15634430568183921464134019 23451645852275882196201029)
            ·
              refine ⟨4397183597301727911787693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23451645852275882196201029 4397183597301727911787693)
              ·
                refine ⟨1648943848988147966920385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4397183597301727911787693 1648943848988147966920385)
                ·
                  refine ⟨1236707886741110975190289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648943848988147966920385 1236707886741110975190289)
                  ·
                    refine ⟨927530915055833231392717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236707886741110975190289 927530915055833231392717)
                    ·
                      refine ⟨347824093145937461772269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927530915055833231392717 347824093145937461772269)
                      ·
                        rfl

theorem cell23_677385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_677385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677385 prefixEnd_677385 := by exact prefixLift 677385
  have htrace : WordTrace (prefixWord ++ tailWord_677385) baseStart_677385 baseEnd_677385 := by
    simpa [prefixWord, tailWord_677385, baseEnd_677385] using wordTrace_append hprefix tailTrace_677385
  have hstable : (prefixWord ++ tailWord_677385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677385).length < 2 ^ (prefixWord ++ tailWord_677385).sum := by decide
  have hdescent : baseEnd_677385 < baseStart_677385 := by decide
  rcases family_descends (prefixWord ++ tailWord_677385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677405 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 6]
def baseStart_677405 : Nat := 118140960795 + 677405 * 2 ^ 59
def prefixEnd_677405 : Nat := 4983230072969 + 3 ^ 40 * 677405 * 2
def baseEnd_677405 : Nat := 38648262528780820391353

theorem tailTrace_677405 : CollatzResearch.WordTrace tailWord_677405 prefixEnd_677405 38648262528780820391353 := by
  unfold tailWord_677405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24706990110884851408433669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16471326740589900938955779 24706990110884851408433669)
  ·
    refine ⟨4632560645790909639081313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24706990110884851408433669 4632560645790909639081313)
    ·
      refine ⟨3474420484343182229310985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4632560645790909639081313 3474420484343182229310985)
      ·
        refine ⟨2605815363257386671983239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3474420484343182229310985 2605815363257386671983239)
        ·
          refine ⟨3908723044886080007974859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605815363257386671983239 3908723044886080007974859)
          ·
            refine ⟨5863084567329120011962289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908723044886080007974859 5863084567329120011962289)
            ·
              refine ⟨4397313425496840008971717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863084567329120011962289 4397313425496840008971717)
              ·
                refine ⟨824496267280657501682197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4397313425496840008971717 824496267280657501682197)
                ·
                  refine ⟨38648262528780820391353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 824496267280657501682197 38648262528780820391353)
                  ·
                    rfl

theorem cell23_677405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_677405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677405 prefixEnd_677405 := by exact prefixLift 677405
  have htrace : WordTrace (prefixWord ++ tailWord_677405) baseStart_677405 baseEnd_677405 := by
    simpa [prefixWord, tailWord_677405, baseEnd_677405] using wordTrace_append hprefix tailTrace_677405
  have hstable : (prefixWord ++ tailWord_677405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677405).length < 2 ^ (prefixWord ++ tailWord_677405).sum := by decide
  have hdescent : baseEnd_677405 < baseStart_677405 := by decide
  rcases family_descends (prefixWord ++ tailWord_677405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677406 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_677406 : Nat := 118140960795 + 677406 * 2 ^ 59
def prefixEnd_677406 : Nat := 4983230072969 + 3 ^ 40 * 677406 * 2
def baseEnd_677406 : Nat := 347834876239681879609673

theorem tailTrace_677406 : CollatzResearch.WordTrace tailWord_677406 prefixEnd_677406 347834876239681879609673 := by
  unfold tailWord_677406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088378322985153572402509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16471351055920819052813381 3088378322985153572402509)
  ·
    refine ⟨1158141871119432589650941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3088378322985153572402509 1158141871119432589650941)
    ·
      refine ⟨434303201669787221119103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1158141871119432589650941 434303201669787221119103)
      ·
        refine ⟨651454802504680831678655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434303201669787221119103 651454802504680831678655)
        ·
          refine ⟨977182203757021247517983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651454802504680831678655 977182203757021247517983)
          ·
            refine ⟨1465773305635531871276975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977182203757021247517983 1465773305635531871276975)
            ·
              refine ⟨2198659958453297806915463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465773305635531871276975 2198659958453297806915463)
              ·
                refine ⟨3297989937679946710373195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198659958453297806915463 3297989937679946710373195)
                ·
                  refine ⟨4946984906519920065559793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297989937679946710373195 4946984906519920065559793)
                  ·
                    refine ⟨3710238679889940049169845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4946984906519920065559793 3710238679889940049169845)
                    ·
                      refine ⟨347834876239681879609673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3710238679889940049169845 347834876239681879609673)
                      ·
                        rfl

theorem cell23_677406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_677406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677406 prefixEnd_677406 := by exact prefixLift 677406
  have htrace : WordTrace (prefixWord ++ tailWord_677406) baseStart_677406 baseEnd_677406 := by
    simpa [prefixWord, tailWord_677406, baseEnd_677406] using wordTrace_append hprefix tailTrace_677406
  have hstable : (prefixWord ++ tailWord_677406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677406).length < 2 ^ (prefixWord ++ tailWord_677406).sum := by decide
  have hdescent : baseEnd_677406 < baseStart_677406 := by decide
  rcases family_descends (prefixWord ++ tailWord_677406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677422 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_677422 : Nat := 118140960795 + 677422 * 2 ^ 59
def prefixEnd_677422 : Nat := 4983230072969 + 3 ^ 40 * 677422 * 2
def baseEnd_677422 : Nat := 38649232436683757445511

theorem tailTrace_677422 : CollatzResearch.WordTrace tailWord_677422 prefixEnd_677422 38649232436683757445511 := by
  unfold tailWord_677422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088451268977907913975315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16471740101215508874535013 3088451268977907913975315)
  ·
    refine ⟨4632676903466861870962973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088451268977907913975315 4632676903466861870962973)
    ·
      refine ⟨1737253838800073201611115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4632676903466861870962973 1737253838800073201611115)
      ·
        refine ⟨2605880758200109802416673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737253838800073201611115 2605880758200109802416673)
        ·
          refine ⟨1954410568650082351812505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605880758200109802416673 1954410568650082351812505)
          ·
            refine ⟨1465807926487561763859379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954410568650082351812505 1465807926487561763859379)
            ·
              refine ⟨2198711889731342645789069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465807926487561763859379 2198711889731342645789069)
              ·
                refine ⟨824516958649253492170901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198711889731342645789069 824516958649253492170901)
                ·
                  refine ⟨38649232436683757445511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 824516958649253492170901 38649232436683757445511)
                  ·
                    rfl

theorem cell23_677422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_677422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677422 prefixEnd_677422 := by exact prefixLift 677422
  have htrace : WordTrace (prefixWord ++ tailWord_677422) baseStart_677422 baseEnd_677422 := by
    simpa [prefixWord, tailWord_677422, baseEnd_677422] using wordTrace_append hprefix tailTrace_677422
  have hstable : (prefixWord ++ tailWord_677422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677422).length < 2 ^ (prefixWord ++ tailWord_677422).sum := by decide
  have hdescent : baseEnd_677422 < baseStart_677422 := by decide
  rcases family_descends (prefixWord ++ tailWord_677422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677465 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_677465 : Nat := 118140960795 + 677465 * 2 ^ 59
def prefixEnd_677465 : Nat := 4983230072969 + 3 ^ 40 * 677465 * 2
def baseEnd_677465 : Nat := 115955057199432382923967

theorem tailTrace_677465 : CollatzResearch.WordTrace tailWord_677465 prefixEnd_677465 115955057199432382923967 := by
  unfold tailWord_677465
  simp only [CollatzResearch.WordTrace]
  refine ⟨24709178490667481655617849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16472785660444987770411899 24709178490667481655617849)
  ·
    refine ⟨18531883868000611241713387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24709178490667481655617849 18531883868000611241713387)
    ·
      refine ⟨27797825802000916862570081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18531883868000611241713387 27797825802000916862570081)
      ·
        refine ⟨20848369351500687646927561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27797825802000916862570081 20848369351500687646927561)
        ·
          refine ⟨15636277013625515735195671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20848369351500687646927561 15636277013625515735195671)
          ·
            refine ⟨23454415520438273602793507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636277013625515735195671 23454415520438273602793507)
            ·
              refine ⟨35181623280657410404190261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23454415520438273602793507 35181623280657410404190261)
              ·
                refine ⟨3298277182561632225392837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35181623280657410404190261 3298277182561632225392837)
                ·
                  refine ⟨618426971730306042261157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3298277182561632225392837 618426971730306042261157)
                  ·
                    refine ⟨115955057199432382923967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618426971730306042261157 115955057199432382923967)
                    ·
                      rfl

theorem cell23_677465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_677465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677465 prefixEnd_677465 := by exact prefixLift 677465
  have htrace : WordTrace (prefixWord ++ tailWord_677465) baseStart_677465 baseEnd_677465 := by
    simpa [prefixWord, tailWord_677465, baseEnd_677465] using wordTrace_append hprefix tailTrace_677465
  have hstable : (prefixWord ++ tailWord_677465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677465).length < 2 ^ (prefixWord ++ tailWord_677465).sum := by decide
  have hdescent : baseEnd_677465 < baseStart_677465 := by decide
  rcases family_descends (prefixWord ++ tailWord_677465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677482 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_677482 : Nat := 118140960795 + 677482 * 2 ^ 59
def prefixEnd_677482 : Nat := 4983230072969 + 3 ^ 40 * 677482 * 2
def baseEnd_677482 : Nat := 115957966923141194086441

theorem tailTrace_677482 : CollatzResearch.WordTrace tailWord_677482 prefixEnd_677482 115957966923141194086441 := by
  unfold tailWord_677482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177449632901473389746675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16473199021070595705991133 6177449632901473389746675)
  ·
    refine ⟨9266174449352210084620013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6177449632901473389746675 9266174449352210084620013)
    ·
      refine ⟨3474815418507078781732505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9266174449352210084620013 3474815418507078781732505)
      ·
        refine ⟨2606111563880309086299379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3474815418507078781732505 2606111563880309086299379)
        ·
          refine ⟨3909167345820463629449069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606111563880309086299379 3909167345820463629449069)
          ·
            refine ⟨1465937754682673861043401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3909167345820463629449069 1465937754682673861043401)
            ·
              refine ⟨1099453316012005395782551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465937754682673861043401 1099453316012005395782551)
              ·
                refine ⟨1649179974018008093673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099453316012005395782551 1649179974018008093673827)
                ·
                  refine ⟨2473769961027012140510741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649179974018008093673827 2473769961027012140510741)
                  ·
                    refine ⟨115957966923141194086441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2473769961027012140510741 115957966923141194086441)
                    ·
                      rfl

theorem cell23_677482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_677482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677482 prefixEnd_677482 := by exact prefixLift 677482
  have htrace : WordTrace (prefixWord ++ tailWord_677482) baseStart_677482 baseEnd_677482 := by
    simpa [prefixWord, tailWord_677482, baseEnd_677482] using wordTrace_append hprefix tailTrace_677482
  have hstable : (prefixWord ++ tailWord_677482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677482).length < 2 ^ (prefixWord ++ tailWord_677482).sum := by decide
  have hdescent : baseEnd_677482 < baseStart_677482 := by decide
  rcases family_descends (prefixWord ++ tailWord_677482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677512 : List Nat := [2, 1, 3, 5, 1, 1, 10]
def baseStart_677512 : Nat := 118140960795 + 677512 * 2 ^ 59
def prefixEnd_677512 : Nat := 4983230072969 + 3 ^ 40 * 677512 * 2
def baseEnd_677512 : Nat := 4294929693692079813385

theorem tailTrace_677512 : CollatzResearch.WordTrace tailWord_677512 prefixEnd_677512 4294929693692079813385 := by
  unfold tailWord_677512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355446360748604341289395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16473928480998139121719193 12355446360748604341289395)
  ·
    refine ⟨18533169541122906511934093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355446360748604341289395 18533169541122906511934093)
    ·
      refine ⟨6949938577921089941975285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18533169541122906511934093 6949938577921089941975285)
      ·
        refine ⟨651556741680102182060183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6949938577921089941975285 651556741680102182060183)
        ·
          refine ⟨977335112520153273090275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651556741680102182060183 977335112520153273090275)
          ·
            refine ⟨1466002668780229909635413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977335112520153273090275 1466002668780229909635413)
            ·
              refine ⟨4294929693692079813385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1466002668780229909635413 4294929693692079813385)
              ·
                rfl

theorem cell23_677512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 10].length) (baseStart_677512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677512 prefixEnd_677512 := by exact prefixLift 677512
  have htrace : WordTrace (prefixWord ++ tailWord_677512) baseStart_677512 baseEnd_677512 := by
    simpa [prefixWord, tailWord_677512, baseEnd_677512] using wordTrace_append hprefix tailTrace_677512
  have hstable : (prefixWord ++ tailWord_677512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677512).length < 2 ^ (prefixWord ++ tailWord_677512).sum := by decide
  have hdescent : baseEnd_677512 < baseStart_677512 := by decide
  rcases family_descends (prefixWord ++ tailWord_677512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677557 : List Nat := [1, 3, 3, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_677557 : Nat := 118140960795 + 677557 * 2 ^ 59
def prefixEnd_677557 : Nat := 4983230072969 + 3 ^ 40 * 677557 * 2
def baseEnd_677557 : Nat := 347912411818510788821479

theorem tailTrace_677557 : CollatzResearch.WordTrace tailWord_677557 prefixEnd_677557 347912411818510788821479 := by
  unfold tailWord_677557
  simp only [CollatzResearch.WordTrace]
  refine ⟨24712534006334181367966925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16475022670889454245311283 24712534006334181367966925)
  ·
    refine ⟨9267200252375318012987597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24712534006334181367966925 9267200252375318012987597)
    ·
      refine ⟨3475200094640744254870349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9267200252375318012987597 3475200094640744254870349)
      ·
        refine ⟨1303200035490279095576381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3475200094640744254870349 1303200035490279095576381)
        ·
          refine ⟨488700013308854660841143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1303200035490279095576381 488700013308854660841143)
          ·
            refine ⟨733050019963281991261715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488700013308854660841143 733050019963281991261715)
            ·
              refine ⟨1099575029944922986892573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733050019963281991261715 1099575029944922986892573)
              ·
                refine ⟨412340636229346120084715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099575029944922986892573 412340636229346120084715)
                ·
                  refine ⟨618510954344019180127073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412340636229346120084715 618510954344019180127073)
                  ·
                    refine ⟨463883215758014385095305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618510954344019180127073 463883215758014385095305)
                    ·
                      refine ⟨347912411818510788821479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463883215758014385095305 347912411818510788821479)
                      ·
                        rfl

theorem cell23_677557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_677557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677557 prefixEnd_677557 := by exact prefixLift 677557
  have htrace : WordTrace (prefixWord ++ tailWord_677557) baseStart_677557 baseEnd_677557 := by
    simpa [prefixWord, tailWord_677557, baseEnd_677557] using wordTrace_append hprefix tailTrace_677557
  have hstable : (prefixWord ++ tailWord_677557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677557).length < 2 ^ (prefixWord ++ tailWord_677557).sum := by decide
  have hdescent : baseEnd_677557 < baseStart_677557 := by decide
  rcases family_descends (prefixWord ++ tailWord_677557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677566 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_677566 : Nat := 118140960795 + 677566 * 2 ^ 59
def prefixEnd_677566 : Nat := 4983230072969 + 3 ^ 40 * 677566 * 2
def baseEnd_677566 : Nat := 347917033144401253608937

theorem tailTrace_677566 : CollatzResearch.WordTrace tailWord_677566 prefixEnd_677566 347917033144401253608937 := by
  unfold tailWord_677566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089107782912696988130569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16475241508867717270029701 3089107782912696988130569)
  ·
    refine ⟨2316830837184522741097927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3089107782912696988130569 2316830837184522741097927)
    ·
      refine ⟨3475246255776784111646891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2316830837184522741097927 3475246255776784111646891)
      ·
        refine ⟨5212869383665176167470337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475246255776784111646891 5212869383665176167470337)
        ·
          refine ⟨3909652037748882125602753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5212869383665176167470337 3909652037748882125602753)
          ·
            refine ⟨2932239028311661594202065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909652037748882125602753 2932239028311661594202065)
            ·
              refine ⟨2199179271233746195651549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932239028311661594202065 2199179271233746195651549)
              ·
                refine ⟨824692226712654823369331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199179271233746195651549 824692226712654823369331)
                ·
                  refine ⟨1237038340068982235053997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 824692226712654823369331 1237038340068982235053997)
                  ·
                    refine ⟨463889377525868338145249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1237038340068982235053997 463889377525868338145249)
                    ·
                      refine ⟨347917033144401253608937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463889377525868338145249 347917033144401253608937)
                      ·
                        rfl

theorem cell23_677566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_677566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677566 prefixEnd_677566 := by exact prefixLift 677566
  have htrace : WordTrace (prefixWord ++ tailWord_677566) baseStart_677566 baseEnd_677566 := by
    simpa [prefixWord, tailWord_677566, baseEnd_677566] using wordTrace_append hprefix tailTrace_677566
  have hstable : (prefixWord ++ tailWord_677566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677566).length < 2 ^ (prefixWord ++ tailWord_677566).sum := by decide
  have hdescent : baseEnd_677566 < baseStart_677566 := by decide
  rcases family_descends (prefixWord ++ tailWord_677566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677574 : List Nat := [6, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_677574 : Nat := 118140960795 + 677574 * 2 ^ 59
def prefixEnd_677574 : Nat := 4983230072969 + 3 ^ 40 * 677574 * 2
def baseEnd_677574 : Nat := 347921140989637222308901

theorem tailTrace_677574 : CollatzResearch.WordTrace tailWord_677574 prefixEnd_677574 347921140989637222308901 := by
  unfold tailWord_677574
  simp only [CollatzResearch.WordTrace]
  refine ⟨772286063977268539729243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16475436031515062180890517 772286063977268539729243)
  ·
    refine ⟨1158429095965902809593865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772286063977268539729243 1158429095965902809593865)
    ·
      refine ⟨868821821974427107195399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158429095965902809593865 868821821974427107195399)
      ·
        refine ⟨1303232732961640660793099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868821821974427107195399 1303232732961640660793099)
        ·
          refine ⟨1954849099442460991189649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303232732961640660793099 1954849099442460991189649)
          ·
            refine ⟨1466136824581845743392237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954849099442460991189649 1466136824581845743392237)
            ·
              refine ⟨549801309218192153772089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1466136824581845743392237 549801309218192153772089)
              ·
                refine ⟨412350981913644115329067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549801309218192153772089 412350981913644115329067)
                ·
                  refine ⟨618526472870466172993601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412350981913644115329067 618526472870466172993601)
                  ·
                    refine ⟨463894854652849629745201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618526472870466172993601 463894854652849629745201)
                    ·
                      refine ⟨347921140989637222308901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463894854652849629745201 347921140989637222308901)
                      ·
                        rfl

theorem cell23_677574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_677574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677574 prefixEnd_677574 := by exact prefixLift 677574
  have htrace : WordTrace (prefixWord ++ tailWord_677574) baseStart_677574 baseEnd_677574 := by
    simpa [prefixWord, tailWord_677574, baseEnd_677574] using wordTrace_append hprefix tailTrace_677574
  have hstable : (prefixWord ++ tailWord_677574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677574).length < 2 ^ (prefixWord ++ tailWord_677574).sum := by decide
  have hdescent : baseEnd_677574 < baseStart_677574 := by decide
  rcases family_descends (prefixWord ++ tailWord_677574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677582 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_677582 : Nat := 118140960795 + 677582 * 2 ^ 59
def prefixEnd_677582 : Nat := 4983230072969 + 3 ^ 40 * 677582 * 2
def baseEnd_677582 : Nat := 347925248834873191008863

theorem tailTrace_677582 : CollatzResearch.WordTrace tailWord_677582 prefixEnd_677582 347925248834873191008863 := by
  unfold tailWord_677582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089180728905451329703375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16475630554162407091751333 3089180728905451329703375)
  ·
    refine ⟨4633771093358176994555063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089180728905451329703375 4633771093358176994555063)
    ·
      refine ⟨6950656640037265491832595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633771093358176994555063 6950656640037265491832595)
      ·
        refine ⟨10425984960055898237748893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6950656640037265491832595 10425984960055898237748893)
        ·
          refine ⟨3909744360020961839155835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10425984960055898237748893 3909744360020961839155835)
          ·
            refine ⟨5864616540031442758733753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909744360020961839155835 5864616540031442758733753)
            ·
              refine ⟨4398462405023582069050315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864616540031442758733753 4398462405023582069050315)
              ·
                refine ⟨6597693607535373103575473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398462405023582069050315 6597693607535373103575473)
                ·
                  refine ⟨4948270205651529827681605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597693607535373103575473 4948270205651529827681605)
                  ·
                    refine ⟨927800663559661842690301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4948270205651529827681605 927800663559661842690301)
                    ·
                      refine ⟨347925248834873191008863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927800663559661842690301 347925248834873191008863)
                      ·
                        rfl

theorem cell23_677582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_677582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677582 prefixEnd_677582 := by exact prefixLift 677582
  have htrace : WordTrace (prefixWord ++ tailWord_677582) baseStart_677582 baseEnd_677582 := by
    simpa [prefixWord, tailWord_677582, baseEnd_677582] using wordTrace_append hprefix tailTrace_677582
  have hstable : (prefixWord ++ tailWord_677582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677582).length < 2 ^ (prefixWord ++ tailWord_677582).sum := by decide
  have hdescent : baseEnd_677582 < baseStart_677582 := by decide
  rcases family_descends (prefixWord ++ tailWord_677582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677590 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_677590 : Nat := 118140960795 + 677590 * 2 ^ 59
def prefixEnd_677590 : Nat := 4983230072969 + 3 ^ 40 * 677590 * 2
def baseEnd_677590 : Nat := 347929356680109159708827

theorem tailTrace_677590 : CollatzResearch.WordTrace tailWord_677590 prefixEnd_677590 347929356680109159708827 := by
  unfold tailWord_677590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544608600950914250244889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16475825076809752002612149 1544608600950914250244889)
  ·
    refine ⟨1158456450713185687683667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1544608600950914250244889 1158456450713185687683667)
    ·
      refine ⟨1737684676069778531525501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158456450713185687683667 1737684676069778531525501)
      ·
        refine ⟨651631753526166949322063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737684676069778531525501 651631753526166949322063)
        ·
          refine ⟨977447630289250423983095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651631753526166949322063 977447630289250423983095)
          ·
            refine ⟨1466171445433875635974643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977447630289250423983095 1466171445433875635974643)
            ·
              refine ⟨2199257168150813453961965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466171445433875635974643 2199257168150813453961965)
              ·
                refine ⟨824721438056555045235737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199257168150813453961965 824721438056555045235737)
                ·
                  refine ⟨618541078542416283926803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824721438056555045235737 618541078542416283926803)
                  ·
                    refine ⟨927811617813624425890205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 618541078542416283926803 927811617813624425890205)
                    ·
                      refine ⟨347929356680109159708827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 927811617813624425890205 347929356680109159708827)
                      ·
                        rfl

theorem cell23_677590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_677590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677590 prefixEnd_677590 := by exact prefixLift 677590
  have htrace : WordTrace (prefixWord ++ tailWord_677590) baseStart_677590 baseEnd_677590 := by
    simpa [prefixWord, tailWord_677590, baseEnd_677590] using wordTrace_append hprefix tailTrace_677590
  have hstable : (prefixWord ++ tailWord_677590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677590).length < 2 ^ (prefixWord ++ tailWord_677590).sum := by decide
  have hdescent : baseEnd_677590 < baseStart_677590 := by decide
  rcases family_descends (prefixWord ++ tailWord_677590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677630 : List Nat := [4, 2, 2, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_677630 : Nat := 118140960795 + 677630 * 2 ^ 59
def prefixEnd_677630 : Nat := 4983230072969 + 3 ^ 40 * 677630 * 2
def baseEnd_677630 : Nat := 347949895906289003208643

theorem tailTrace_677630 : CollatzResearch.WordTrace tailWord_677630 prefixEnd_677630 347949895906289003208643 := by
  unfold tailWord_677630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089399566883714354421793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16476797690046476556916229 3089399566883714354421793)
  ·
    refine ⟨2317049675162785765816345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3089399566883714354421793 2317049675162785765816345)
    ·
      refine ⟨1737787256372089324362259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317049675162785765816345 1737787256372089324362259)
      ·
        refine ⟨2606680884558133986543389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737787256372089324362259 2606680884558133986543389)
        ·
          refine ⟨977505331709300244953771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2606680884558133986543389 977505331709300244953771)
          ·
            refine ⟨1466257997563950367430657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977505331709300244953771 1466257997563950367430657)
            ·
              refine ⟨1099693498172962775572993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466257997563950367430657 1099693498172962775572993)
              ·
                refine ⟨824770123629722081679745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099693498172962775572993 824770123629722081679745)
                ·
                  refine ⟨618577592722291561259809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824770123629722081679745 618577592722291561259809)
                  ·
                    refine ⟨463933194541718670944857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618577592722291561259809 463933194541718670944857)
                    ·
                      refine ⟨347949895906289003208643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 463933194541718670944857 347949895906289003208643)
                      ·
                        rfl

theorem cell23_677630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_677630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677630 prefixEnd_677630 := by exact prefixLift 677630
  have htrace : WordTrace (prefixWord ++ tailWord_677630) baseStart_677630 baseEnd_677630 := by
    simpa [prefixWord, tailWord_677630, baseEnd_677630] using wordTrace_append hprefix tailTrace_677630
  have hstable : (prefixWord ++ tailWord_677630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677630).length < 2 ^ (prefixWord ++ tailWord_677630).sum := by decide
  have hdescent : baseEnd_677630 < baseStart_677630 := by decide
  rcases family_descends (prefixWord ++ tailWord_677630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677636 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 5]
def baseStart_677636 : Nat := 118140960795 + 677636 * 2 ^ 59
def prefixEnd_677636 : Nat := 4983230072969 + 3 ^ 40 * 677636 * 2
def baseEnd_677636 : Nat := 38661441865579553303735

theorem tailTrace_677636 : CollatzResearch.WordTrace tailWord_677636 prefixEnd_677636 38661441865579553303735 := by
  unfold tailWord_677636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12357707686523988930046381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16476943582031985240061841 12357707686523988930046381)
  ·
    refine ⟨4634140382446495848767393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12357707686523988930046381 4634140382446495848767393)
    ·
      refine ⟨3475605286834871886575545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4634140382446495848767393 3475605286834871886575545)
      ·
        refine ⟨2606703965126153914931659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3475605286834871886575545 2606703965126153914931659)
        ·
          refine ⟨3910055947689230872397489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606703965126153914931659 3910055947689230872397489)
          ·
            refine ⟨2932541960766923154298117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910055947689230872397489 2932541960766923154298117)
            ·
              refine ⟨549851617643798091430897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2932541960766923154298117 549851617643798091430897)
              ·
                refine ⟨412388713232848568573173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549851617643798091430897 412388713232848568573173)
                ·
                  refine ⟨38661441865579553303735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412388713232848568573173 38661441865579553303735)
                  ·
                    rfl

theorem cell23_677636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_677636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677636 prefixEnd_677636 := by exact prefixLift 677636
  have htrace : WordTrace (prefixWord ++ tailWord_677636) baseStart_677636 baseEnd_677636 := by
    simpa [prefixWord, tailWord_677636, baseEnd_677636] using wordTrace_append hprefix tailTrace_677636
  have hstable : (prefixWord ++ tailWord_677636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677636).length < 2 ^ (prefixWord ++ tailWord_677636).sum := by decide
  have hdescent : baseEnd_677636 < baseStart_677636 := by decide
  rcases family_descends (prefixWord ++ tailWord_677636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677642 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_677642 : Nat := 118140960795 + 677642 * 2 ^ 59
def prefixEnd_677642 : Nat := 4983230072969 + 3 ^ 40 * 677642 * 2
def baseEnd_677642 : Nat := 347956057674142956258587

theorem tailTrace_677642 : CollatzResearch.WordTrace tailWord_677642 prefixEnd_677642 347956057674142956258587 := by
  unfold tailWord_677642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178908552756560221202795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16477089474017493923207453 6178908552756560221202795)
  ·
    refine ⟨9268362829134840331804193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178908552756560221202795 9268362829134840331804193)
    ·
      refine ⟨6951272121851130248853145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9268362829134840331804193 6951272121851130248853145)
      ·
        refine ⟨5213454091388347686639859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6951272121851130248853145 5213454091388347686639859)
        ·
          refine ⟨7820181137082521529959789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213454091388347686639859 7820181137082521529959789)
          ·
            refine ⟨2932567926405945573734921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7820181137082521529959789 2932567926405945573734921)
            ·
              refine ⟨2199425944804459180301191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932567926405945573734921 2199425944804459180301191)
              ·
                refine ⟨3299138917206688770451787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199425944804459180301191 3299138917206688770451787)
                ·
                  refine ⟨4948708375810033155677681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299138917206688770451787 4948708375810033155677681)
                  ·
                    refine ⟨3711531281857524866758261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4948708375810033155677681 3711531281857524866758261)
                    ·
                      refine ⟨347956057674142956258587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3711531281857524866758261 347956057674142956258587)
                      ·
                        rfl

theorem cell23_677642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_677642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677642 prefixEnd_677642 := by exact prefixLift 677642
  have htrace : WordTrace (prefixWord ++ tailWord_677642) baseStart_677642 baseEnd_677642 := by
    simpa [prefixWord, tailWord_677642, baseEnd_677642] using wordTrace_append hprefix tailTrace_677642
  have hstable : (prefixWord ++ tailWord_677642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677642).length < 2 ^ (prefixWord ++ tailWord_677642).sum := by decide
  have hdescent : baseEnd_677642 < baseStart_677642 := by decide
  rcases family_descends (prefixWord ++ tailWord_677642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677669 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_677669 : Nat := 118140960795 + 677669 * 2 ^ 59
def prefixEnd_677669 : Nat := 4983230072969 + 3 ^ 40 * 677669 * 2
def baseEnd_677669 : Nat := 347969921651814350620963

theorem tailTrace_677669 : CollatzResearch.WordTrace tailWord_677669 prefixEnd_677669 347969921651814350620963 := by
  unfold tailWord_677669
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716618981928424496044061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16477745987952282997362707 24716618981928424496044061)
  ·
    refine ⟨9268732118223159186016523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24716618981928424496044061 9268732118223159186016523)
    ·
      refine ⟨13903098177334738779024785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268732118223159186016523 13903098177334738779024785)
      ·
        refine ⟨10427323633001054084268589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13903098177334738779024785 10427323633001054084268589)
        ·
          refine ⟨3910246362375395281600721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10427323633001054084268589 3910246362375395281600721)
          ·
            refine ⟨2932684771781546461200541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910246362375395281600721 2932684771781546461200541)
            ·
              refine ⟨1099756789418079922950203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2932684771781546461200541 1099756789418079922950203)
              ·
                refine ⟨1649635184127119884425305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099756789418079922950203 1649635184127119884425305)
                ·
                  refine ⟨1237226388095339913318979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1649635184127119884425305 1237226388095339913318979)
                  ·
                    refine ⟨1855839582143009869978469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1237226388095339913318979 1855839582143009869978469)
                    ·
                      refine ⟨347969921651814350620963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1855839582143009869978469 347969921651814350620963)
                      ·
                        rfl

theorem cell23_677669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_677669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677669 prefixEnd_677669 := by exact prefixLift 677669
  have htrace : WordTrace (prefixWord ++ tailWord_677669) baseStart_677669 baseEnd_677669 := by
    simpa [prefixWord, tailWord_677669, baseEnd_677669] using wordTrace_append hprefix tailTrace_677669
  have hstable : (prefixWord ++ tailWord_677669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677669).length < 2 ^ (prefixWord ++ tailWord_677669).sum := by decide
  have hdescent : baseEnd_677669 < baseStart_677669 := by decide
  rcases family_descends (prefixWord ++ tailWord_677669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677682 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_677682 : Nat := 118140960795 + 677682 * 2 ^ 59
def prefixEnd_677682 : Nat := 4983230072969 + 3 ^ 40 * 677682 * 2
def baseEnd_677682 : Nat := 347976596900322799758403

theorem tailTrace_677682 : CollatzResearch.WordTrace tailWord_677682 prefixEnd_677682 347976596900322799758403 := by
  unfold tailWord_677682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179273282720331929066825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16478062087254218477511533 6179273282720331929066825)
  ·
    refine ⟨4634454962040248946800119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6179273282720331929066825 4634454962040248946800119)
    ·
      refine ⟨6951682443060373420200179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4634454962040248946800119 6951682443060373420200179)
      ·
        refine ⟨10427523664590560130300269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6951682443060373420200179 10427523664590560130300269)
        ·
          refine ⟨3910321374221460048862601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10427523664590560130300269 3910321374221460048862601)
          ·
            refine ⟨2932741030666095036646951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910321374221460048862601 2932741030666095036646951)
            ·
              refine ⟨4399111545999142554970427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932741030666095036646951 4399111545999142554970427)
              ·
                refine ⟨6598667318998713832455641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399111545999142554970427 6598667318998713832455641)
                ·
                  refine ⟨4949000489249035374341731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6598667318998713832455641 4949000489249035374341731)
                  ·
                    refine ⟨7423500733873553061512597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4949000489249035374341731 7423500733873553061512597)
                    ·
                      refine ⟨347976596900322799758403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7423500733873553061512597 347976596900322799758403)
                      ·
                        rfl

theorem cell23_677682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_677682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677682 prefixEnd_677682 := by exact prefixLift 677682
  have htrace : WordTrace (prefixWord ++ tailWord_677682) baseStart_677682 baseEnd_677682 := by
    simpa [prefixWord, tailWord_677682, baseEnd_677682] using wordTrace_append hprefix tailTrace_677682
  have hstable : (prefixWord ++ tailWord_677682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677682).length < 2 ^ (prefixWord ++ tailWord_677682).sum := by decide
  have hdescent : baseEnd_677682 < baseStart_677682 := by decide
  rcases family_descends (prefixWord ++ tailWord_677682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677729 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_677729 : Nat := 118140960795 + 677729 * 2 ^ 59
def prefixEnd_677729 : Nat := 4983230072969 + 3 ^ 40 * 677729 * 2
def baseEnd_677729 : Nat := 348000730491084115870687

theorem tailTrace_677729 : CollatzResearch.WordTrace tailWord_677729 prefixEnd_677729 348000730491084115870687 := by
  unfold tailWord_677729
  simp only [CollatzResearch.WordTrace]
  refine ⟨24718807361711054743228241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16479204907807369828818827 24718807361711054743228241)
  ·
    refine ⟨18539105521283291057421181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24718807361711054743228241 18539105521283291057421181)
    ·
      refine ⟨6952164570481234146532943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18539105521283291057421181 6952164570481234146532943)
      ·
        refine ⟨10428246855721851219799415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6952164570481234146532943 10428246855721851219799415)
        ·
          refine ⟨15642370283582776829699123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10428246855721851219799415 15642370283582776829699123)
          ·
            refine ⟨23463555425374165244548685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15642370283582776829699123 23463555425374165244548685)
            ·
              refine ⟨8798833284515311966705757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23463555425374165244548685 8798833284515311966705757)
              ·
                refine ⟨3299562481693241987514659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8798833284515311966705757 3299562481693241987514659)
                ·
                  refine ⟨4949343722539862981271989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3299562481693241987514659 4949343722539862981271989)
                  ·
                    refine ⟨464000973988112154494249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4949343722539862981271989 464000973988112154494249)
                    ·
                      refine ⟨348000730491084115870687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464000973988112154494249 348000730491084115870687)
                      ·
                        rfl

theorem cell23_677729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_677729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677729 prefixEnd_677729 := by exact prefixLift 677729
  have htrace : WordTrace (prefixWord ++ tailWord_677729) baseStart_677729 baseEnd_677729 := by
    simpa [prefixWord, tailWord_677729, baseEnd_677729] using wordTrace_append hprefix tailTrace_677729
  have hstable : (prefixWord ++ tailWord_677729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677729).length < 2 ^ (prefixWord ++ tailWord_677729).sum := by decide
  have hdescent : baseEnd_677729 < baseStart_677729 := by decide
  rcases family_descends (prefixWord ++ tailWord_677729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677730 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_677730 : Nat := 118140960795 + 677730 * 2 ^ 59
def prefixEnd_677730 : Nat := 4983230072969 + 3 ^ 40 * 677730 * 2
def baseEnd_677730 : Nat := 116000414657246203986061

theorem tailTrace_677730 : CollatzResearch.WordTrace tailWord_677730 prefixEnd_677730 116000414657246203986061 := by
  unfold tailWord_677730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179710958676857978503661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16479229223138287942676429 6179710958676857978503661)
  ·
    refine ⟨2317391609503821741938873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6179710958676857978503661 2317391609503821741938873)
    ·
      refine ⟨1738043707127866306454155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317391609503821741938873 1738043707127866306454155)
      ·
        refine ⟨2607065560691799459681233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738043707127866306454155 2607065560691799459681233)
        ·
          refine ⟨1955299170518849594760925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607065560691799459681233 1955299170518849594760925)
          ·
            refine ⟨733237188944568598035347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1955299170518849594760925 733237188944568598035347)
            ·
              refine ⟨1099855783416852897053021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733237188944568598035347 1099855783416852897053021)
              ·
                refine ⟨412445918781319836394883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099855783416852897053021 412445918781319836394883)
                ·
                  refine ⟨618668878171979754592325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412445918781319836394883 618668878171979754592325)
                  ·
                    refine ⟨116000414657246203986061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618668878171979754592325 116000414657246203986061)
                    ·
                      rfl

theorem cell23_677730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_677730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677730 prefixEnd_677730 := by exact prefixLift 677730
  have htrace : WordTrace (prefixWord ++ tailWord_677730) baseStart_677730 baseEnd_677730 := by
    simpa [prefixWord, tailWord_677730, baseEnd_677730] using wordTrace_append hprefix tailTrace_677730
  have hstable : (prefixWord ++ tailWord_677730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677730).length < 2 ^ (prefixWord ++ tailWord_677730).sum := by decide
  have hdescent : baseEnd_677730 < baseStart_677730 := by decide
  rcases family_descends (prefixWord ++ tailWord_677730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677789 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_677789 : Nat := 118140960795 + 677789 * 2 ^ 59
def prefixEnd_677789 : Nat := 4983230072969 + 3 ^ 40 * 677789 * 2
def baseEnd_677789 : Nat := 348031539330353881120411

theorem tailTrace_677789 : CollatzResearch.WordTrace tailWord_677789 prefixEnd_677789 348031539330353881120411 := by
  unfold tailWord_677789
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720995741493684990412421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16480663827662456660274947 24720995741493684990412421)
  ·
    refine ⟨4635186701530065935702329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24720995741493684990412421 4635186701530065935702329)
    ·
      refine ⟨3476390026147549451776747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4635186701530065935702329 3476390026147549451776747)
      ·
        refine ⟨5214585039221324177665121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476390026147549451776747 5214585039221324177665121)
        ·
          refine ⟨3910938779415993133248841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5214585039221324177665121 3910938779415993133248841)
          ·
            refine ⟨2933204084561994849936631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910938779415993133248841 2933204084561994849936631)
            ·
              refine ⟨4399806126842992274904947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933204084561994849936631 4399806126842992274904947)
              ·
                refine ⟨6599709190264488412357421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399806126842992274904947 6599709190264488412357421)
                ·
                  refine ⟨2474890946349183154634033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6599709190264488412357421 2474890946349183154634033)
                  ·
                    refine ⟨1856168209761887365975525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2474890946349183154634033 1856168209761887365975525)
                    ·
                      refine ⟨348031539330353881120411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1856168209761887365975525 348031539330353881120411)
                      ·
                        rfl

theorem cell23_677789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_677789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677789 prefixEnd_677789 := by exact prefixLift 677789
  have htrace : WordTrace (prefixWord ++ tailWord_677789) baseStart_677789 baseEnd_677789 := by
    simpa [prefixWord, tailWord_677789, baseEnd_677789] using wordTrace_append hprefix tailTrace_677789
  have hstable : (prefixWord ++ tailWord_677789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677789).length < 2 ^ (prefixWord ++ tailWord_677789).sum := by decide
  have hdescent : baseEnd_677789 < baseStart_677789 := by decide
  rcases family_descends (prefixWord ++ tailWord_677789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677796 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_677796 : Nat := 118140960795 + 677796 * 2 ^ 59
def prefixEnd_677796 : Nat := 4983230072969 + 3 ^ 40 * 677796 * 2
def baseEnd_677796 : Nat := 348035133694935353732879

theorem tailTrace_677796 : CollatzResearch.WordTrace tailWord_677796 prefixEnd_677796 348035133694935353732879 := by
  unfold tailWord_677796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360625526234162592958621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16480834034978883457278161 12360625526234162592958621)
  ·
    refine ⟨4635234572337810972359483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12360625526234162592958621 4635234572337810972359483)
    ·
      refine ⟨6952851858506716458539225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4635234572337810972359483 6952851858506716458539225)
      ·
        refine ⟨5214638893880037343904419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6952851858506716458539225 5214638893880037343904419)
        ·
          refine ⟨7821958340820056015856629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5214638893880037343904419 7821958340820056015856629)
          ·
            refine ⟨733308594451880251486559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7821958340820056015856629 733308594451880251486559)
            ·
              refine ⟨1099962891677820377229839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733308594451880251486559 1099962891677820377229839)
              ·
                refine ⟨1649944337516730565844759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099962891677820377229839 1649944337516730565844759)
                ·
                  refine ⟨2474916506275095848767139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649944337516730565844759 2474916506275095848767139)
                  ·
                    refine ⟨3712374759412643773150709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2474916506275095848767139 3712374759412643773150709)
                    ·
                      refine ⟨348035133694935353732879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3712374759412643773150709 348035133694935353732879)
                      ·
                        rfl

theorem cell23_677796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_677796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677796 prefixEnd_677796 := by exact prefixLift 677796
  have htrace : WordTrace (prefixWord ++ tailWord_677796) baseStart_677796 baseEnd_677796 := by
    simpa [prefixWord, tailWord_677796, baseEnd_677796] using wordTrace_append hprefix tailTrace_677796
  have hstable : (prefixWord ++ tailWord_677796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677796).length < 2 ^ (prefixWord ++ tailWord_677796).sum := by decide
  have hdescent : baseEnd_677796 < baseStart_677796 := by decide
  rcases family_descends (prefixWord ++ tailWord_677796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677819 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 7, 2]
def baseStart_677819 : Nat := 118140960795 + 677819 * 2 ^ 59
def prefixEnd_677819 : Nat := 4983230072969 + 3 ^ 40 * 677819 * 2
def baseEnd_677819 : Nat := 348046943749988763745273

theorem tailTrace_677819 : CollatzResearch.WordTrace tailWord_677819 prefixEnd_677819 348046943749988763745273 := by
  unfold tailWord_677819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24722089931385000114004511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16481393287590000076003007 24722089931385000114004511)
  ·
    refine ⟨37083134897077500171006767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24722089931385000114004511 37083134897077500171006767)
    ·
      refine ⟨55624702345616250256510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37083134897077500171006767 55624702345616250256510151)
      ·
        refine ⟨83437053518424375384765227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55624702345616250256510151 83437053518424375384765227)
        ·
          refine ⟨125155580277636563077147841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83437053518424375384765227 125155580277636563077147841)
          ·
            refine ⟨93866685208227422307860881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125155580277636563077147841 93866685208227422307860881)
            ·
              refine ⟨70400013906170566730895661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93866685208227422307860881 70400013906170566730895661)
              ·
                refine ⟨26400005214813962524085873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70400013906170566730895661 26400005214813962524085873)
                ·
                  refine ⟨19800003911110471893064405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26400005214813962524085873 19800003911110471893064405)
                  ·
                    refine ⟨464062591666651684993697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19800003911110471893064405 464062591666651684993697)
                    ·
                      refine ⟨348046943749988763745273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464062591666651684993697 348046943749988763745273)
                      ·
                        rfl

theorem cell23_677819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 7, 2].length) (baseStart_677819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677819 prefixEnd_677819 := by exact prefixLift 677819
  have htrace : WordTrace (prefixWord ++ tailWord_677819) baseStart_677819 baseEnd_677819 := by
    simpa [prefixWord, tailWord_677819, baseEnd_677819] using wordTrace_append hprefix tailTrace_677819
  have hstable : (prefixWord ++ tailWord_677819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677819).length < 2 ^ (prefixWord ++ tailWord_677819).sum := by decide
  have hdescent : baseEnd_677819 < baseStart_677819 := by decide
  rcases family_descends (prefixWord ++ tailWord_677819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677859 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 6]
def baseStart_677859 : Nat := 118140960795 + 677859 * 2 ^ 59
def prefixEnd_677859 : Nat := 4983230072969 + 3 ^ 40 * 677859 * 2
def baseEnd_677859 : Nat := 116022494325389535748363

theorem tailTrace_677859 : CollatzResearch.WordTrace tailWord_677859 prefixEnd_677859 116022494325389535748363 := by
  unfold tailWord_677859
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723548851240086945460631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16482365900826724630307087 24723548851240086945460631)
  ·
    refine ⟨37085323276860130418190947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24723548851240086945460631 37085323276860130418190947)
    ·
      refine ⟨55627984915290195627286421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37085323276860130418190947 55627984915290195627286421)
      ·
        refine ⟨2607561792904227920029051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55627984915290195627286421 2607561792904227920029051)
        ·
          refine ⟨3911342689356341880043577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607561792904227920029051 3911342689356341880043577)
          ·
            refine ⟨2933507017017256410032683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911342689356341880043577 2933507017017256410032683)
            ·
              refine ⟨4400260525525884615049025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933507017017256410032683 4400260525525884615049025)
              ·
                refine ⟨3300195394144413461286769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4400260525525884615049025 3300195394144413461286769)
                ·
                  refine ⟨2475146545608310095965077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300195394144413461286769 2475146545608310095965077)
                  ·
                    refine ⟨116022494325389535748363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2475146545608310095965077 116022494325389535748363)
                    ·
                      rfl

theorem cell23_677859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_677859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677859 prefixEnd_677859 := by exact prefixLift 677859
  have htrace : WordTrace (prefixWord ++ tailWord_677859) baseStart_677859 baseEnd_677859 := by
    simpa [prefixWord, tailWord_677859, baseEnd_677859] using wordTrace_append hprefix tailTrace_677859
  have hstable : (prefixWord ++ tailWord_677859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677859).length < 2 ^ (prefixWord ++ tailWord_677859).sum := by decide
  have hdescent : baseEnd_677859 < baseStart_677859 := by decide
  rcases family_descends (prefixWord ++ tailWord_677859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677883 : List Nat := [1, 1, 1, 1, 1, 3, 4, 5, 2, 2, 2]
def baseStart_677883 : Nat := 118140960795 + 677883 * 2 ^ 59
def prefixEnd_677883 : Nat := 4983230072969 + 3 ^ 40 * 677883 * 2
def baseEnd_677883 : Nat := 348079806511876513344979

theorem tailTrace_677883 : CollatzResearch.WordTrace tailWord_677883 prefixEnd_677883 348079806511876513344979 := by
  unfold tailWord_677883
  simp only [CollatzResearch.WordTrace]
  refine ⟨24724424203153139044334303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16482949468768759362889535 24724424203153139044334303)
  ·
    refine ⟨37086636304729708566501455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24724424203153139044334303 37086636304729708566501455)
    ·
      refine ⟨55629954457094562849752183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37086636304729708566501455 55629954457094562849752183)
      ·
        refine ⟨83444931685641844274628275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55629954457094562849752183 83444931685641844274628275)
        ·
          refine ⟨125167397528462766411942413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83444931685641844274628275 125167397528462766411942413)
          ·
            refine ⟨46937774073173537404478405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125167397528462766411942413 46937774073173537404478405)
            ·
              refine ⟨8800832638720038263339701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46937774073173537404478405 8800832638720038263339701)
              ·
                refine ⟨825078059880003587188097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8800832638720038263339701 825078059880003587188097)
                ·
                  refine ⟨618808544910002690391073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825078059880003587188097 618808544910002690391073)
                  ·
                    refine ⟨464106408682502017793305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618808544910002690391073 464106408682502017793305)
                    ·
                      refine ⟨348079806511876513344979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464106408682502017793305 348079806511876513344979)
                      ·
                        rfl

theorem cell23_677883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 2, 2].length) (baseStart_677883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677883 prefixEnd_677883 := by exact prefixLift 677883
  have htrace : WordTrace (prefixWord ++ tailWord_677883) baseStart_677883 baseEnd_677883 := by
    simpa [prefixWord, tailWord_677883, baseEnd_677883] using wordTrace_append hprefix tailTrace_677883
  have hstable : (prefixWord ++ tailWord_677883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677883).length < 2 ^ (prefixWord ++ tailWord_677883).sum := by decide
  have hdescent : baseEnd_677883 < baseStart_677883 := by decide
  rcases family_descends (prefixWord ++ tailWord_677883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677889 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 7]
def baseStart_677889 : Nat := 118140960795 + 677889 * 2 ^ 59
def prefixEnd_677889 : Nat := 4983230072969 + 3 ^ 40 * 677889 * 2
def baseEnd_677889 : Nat := 38675876377311498874439

theorem tailTrace_677889 : CollatzResearch.WordTrace tailWord_677889 prefixEnd_677889 38675876377311498874439 := by
  unfold tailWord_677889
  simp only [CollatzResearch.WordTrace]
  refine ⟨24724643041131402069052721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16483095360754268046035147 24724643041131402069052721)
  ·
    refine ⟨18543482280848551551789541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24724643041131402069052721 18543482280848551551789541)
    ·
      refine ⟨3476902927659103415960539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18543482280848551551789541 3476902927659103415960539)
      ·
        refine ⟨5215354391488655123940809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476902927659103415960539 5215354391488655123940809)
        ·
          refine ⟨3911515793616491342955607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5215354391488655123940809 3911515793616491342955607)
          ·
            refine ⟨5867273690424737014433411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911515793616491342955607 5867273690424737014433411)
            ·
              refine ⟨8800910535637105521650117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867273690424737014433411 8800910535637105521650117)
              ·
                refine ⟨1650170725431957285309397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8800910535637105521650117 1650170725431957285309397)
                ·
                  refine ⟨38675876377311498874439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1650170725431957285309397 38675876377311498874439)
                  ·
                    rfl

theorem cell23_677889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_677889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677889 prefixEnd_677889 := by exact prefixLift 677889
  have htrace : WordTrace (prefixWord ++ tailWord_677889) baseStart_677889 baseEnd_677889 := by
    simpa [prefixWord, tailWord_677889, baseEnd_677889] using wordTrace_append hprefix tailTrace_677889
  have hstable : (prefixWord ++ tailWord_677889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677889).length < 2 ^ (prefixWord ++ tailWord_677889).sum := by decide
  have hdescent : baseEnd_677889 < baseStart_677889 := by decide
  rcases family_descends (prefixWord ++ tailWord_677889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677923 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 5]
def baseStart_677923 : Nat := 118140960795 + 677923 * 2 ^ 59
def prefixEnd_677923 : Nat := 4983230072969 + 3 ^ 40 * 677923 * 2
def baseEnd_677923 : Nat := 38677816193117372982755

theorem tailTrace_677923 : CollatzResearch.WordTrace tailWord_677923 prefixEnd_677923 38677816193117372982755 := by
  unfold tailWord_677923
  simp only [CollatzResearch.WordTrace]
  refine ⟨24725883123008225875790423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16483922082005483917193615 24725883123008225875790423)
  ·
    refine ⟨37088824684512338813685635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24725883123008225875790423 37088824684512338813685635)
    ·
      refine ⟨55633237026768508220528453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37088824684512338813685635 55633237026768508220528453)
      ·
        refine ⟨10431231942519095291349085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55633237026768508220528453 10431231942519095291349085)
        ·
          refine ⟨3911711978444660734255907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10431231942519095291349085 3911711978444660734255907)
          ·
            refine ⟨5867567967666991101383861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911711978444660734255907 5867567967666991101383861)
            ·
              refine ⟨550084496968780415754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5867567967666991101383861 550084496968780415754737)
              ·
                refine ⟨412563372726585311816053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550084496968780415754737 412563372726585311816053)
                ·
                  refine ⟨38677816193117372982755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412563372726585311816053 38677816193117372982755)
                  ·
                    rfl

theorem cell23_677923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 5].length) (baseStart_677923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677923 prefixEnd_677923 := by exact prefixLift 677923
  have htrace : WordTrace (prefixWord ++ tailWord_677923) baseStart_677923 baseEnd_677923 := by
    simpa [prefixWord, tailWord_677923, baseEnd_677923] using wordTrace_append hprefix tailTrace_677923
  have hstable : (prefixWord ++ tailWord_677923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677923).length < 2 ^ (prefixWord ++ tailWord_677923).sum := by decide
  have hdescent : baseEnd_677923 < baseStart_677923 := by decide
  rcases family_descends (prefixWord ++ tailWord_677923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677934 : List Nat := [4, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_677934 : Nat := 118140960795 + 677934 * 2 ^ 59
def prefixEnd_677934 : Nat := 4983230072969 + 3 ^ 40 * 677934 * 2
def baseEnd_677934 : Nat := 348105994025255813807245

theorem tailTrace_677934 : CollatzResearch.WordTrace tailWord_677934 prefixEnd_677934 348105994025255813807245 := by
  unfold tailWord_677934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090785540746046844305107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16484189550645583169627237 3090785540746046844305107)
  ·
    refine ⟨4636178311119070266457661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3090785540746046844305107 4636178311119070266457661)
    ·
      refine ⟨1738566866669651349921623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4636178311119070266457661 1738566866669651349921623)
      ·
        refine ⟨2607850300004477024882435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738566866669651349921623 2607850300004477024882435)
        ·
          refine ⟨3911775450006715537323653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607850300004477024882435 3911775450006715537323653)
          ·
            refine ⟨733457896876259163248185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3911775450006715537323653 733457896876259163248185)
            ·
              refine ⟨550093422657194372436139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733457896876259163248185 550093422657194372436139)
              ·
                refine ⟨825140133985791558654209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550093422657194372436139 825140133985791558654209)
                ·
                  refine ⟨618855100489343668990657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825140133985791558654209 618855100489343668990657)
                  ·
                    refine ⟨464141325367007751742993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618855100489343668990657 464141325367007751742993)
                    ·
                      refine ⟨348105994025255813807245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464141325367007751742993 348105994025255813807245)
                      ·
                        rfl

theorem cell23_677934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_677934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677934 prefixEnd_677934 := by exact prefixLift 677934
  have htrace : WordTrace (prefixWord ++ tailWord_677934) baseStart_677934 baseEnd_677934 := by
    simpa [prefixWord, tailWord_677934, baseEnd_677934] using wordTrace_append hprefix tailTrace_677934
  have hstable : (prefixWord ++ tailWord_677934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677934).length < 2 ^ (prefixWord ++ tailWord_677934).sum := by decide
  have hdescent : baseEnd_677934 < baseStart_677934 := by decide
  rcases family_descends (prefixWord ++ tailWord_677934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677939 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_677939 : Nat := 118140960795 + 677939 * 2 ^ 59
def prefixEnd_677939 : Nat := 4983230072969 + 3 ^ 40 * 677939 * 2
def baseEnd_677939 : Nat := 348108561428528294244721

theorem tailTrace_677939 : CollatzResearch.WordTrace tailWord_677939 prefixEnd_677939 348108561428528294244721 := by
  unfold tailWord_677939
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726466690950260608372871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16484311127300173738915247 24726466690950260608372871)
  ·
    refine ⟨37089700036425390912559307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24726466690950260608372871 37089700036425390912559307)
    ·
      refine ⟨55634550054638086368838961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37089700036425390912559307 55634550054638086368838961)
      ·
        refine ⟨41725912540978564776629221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55634550054638086368838961 41725912540978564776629221)
        ·
          refine ⟨7823608601433480895617979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41725912540978564776629221 7823608601433480895617979)
          ·
            refine ⟨11735412902150221343426969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823608601433480895617979 11735412902150221343426969)
            ·
              refine ⟨8801559676612666007570227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11735412902150221343426969 8801559676612666007570227)
              ·
                refine ⟨13202339514918999011355341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801559676612666007570227 13202339514918999011355341)
                ·
                  refine ⟨4950877318094624629258253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13202339514918999011355341 4950877318094624629258253)
                  ·
                    refine ⟨1856578994285484235971845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4950877318094624629258253 1856578994285484235971845)
                    ·
                      refine ⟨348108561428528294244721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1856578994285484235971845 348108561428528294244721)
                      ·
                        rfl

theorem cell23_677939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_677939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677939 prefixEnd_677939 := by exact prefixLift 677939
  have htrace : WordTrace (prefixWord ++ tailWord_677939) baseStart_677939 baseEnd_677939 := by
    simpa [prefixWord, tailWord_677939, baseEnd_677939] using wordTrace_append hprefix tailTrace_677939
  have hstable : (prefixWord ++ tailWord_677939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677939).length < 2 ^ (prefixWord ++ tailWord_677939).sum := by decide
  have hdescent : baseEnd_677939 < baseStart_677939 := by decide
  rcases family_descends (prefixWord ++ tailWord_677939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677953 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_677953 : Nat := 118140960795 + 677953 * 2 ^ 59
def prefixEnd_677953 : Nat := 4983230072969 + 3 ^ 40 * 677953 * 2
def baseEnd_677953 : Nat := 116038583385897079823219

theorem tailTrace_677953 : CollatzResearch.WordTrace tailWord_677953 prefixEnd_677953 116038583385897079823219 := by
  unfold tailWord_677953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726977312899540999382513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16484651541933027332921675 24726977312899540999382513)
  ·
    refine ⟨18545232984674655749536885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24726977312899540999382513 18545232984674655749536885)
    ·
      refine ⟨1738615592313248976519083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18545232984674655749536885 1738615592313248976519083)
      ·
        refine ⟨2607923388469873464778625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738615592313248976519083 2607923388469873464778625)
        ·
          refine ⟨1955942541352405098583969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607923388469873464778625 1955942541352405098583969)
          ·
            refine ⟨1466956906014303823937977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1955942541352405098583969 1466956906014303823937977)
            ·
              refine ⟨1100217679510727867953483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466956906014303823937977 1100217679510727867953483)
              ·
                refine ⟨1650326519266091801930225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100217679510727867953483 1650326519266091801930225)
                ·
                  refine ⟨1237744889449568851447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1650326519266091801930225 1237744889449568851447669)
                  ·
                    refine ⟨116038583385897079823219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1237744889449568851447669 116038583385897079823219)
                    ·
                      rfl

theorem cell23_677953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_677953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677953 prefixEnd_677953 := by exact prefixLift 677953
  have htrace : WordTrace (prefixWord ++ tailWord_677953) baseStart_677953 baseEnd_677953 := by
    simpa [prefixWord, tailWord_677953, baseEnd_677953] using wordTrace_append hprefix tailTrace_677953
  have hstable : (prefixWord ++ tailWord_677953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677953).length < 2 ^ (prefixWord ++ tailWord_677953).sum := by decide
  have hdescent : baseEnd_677953 < baseStart_677953 := by decide
  rcases family_descends (prefixWord ++ tailWord_677953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677969 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_677969 : Nat := 118140960795 + 677969 * 2 ^ 59
def prefixEnd_677969 : Nat := 4983230072969 + 3 ^ 40 * 677969 * 2
def baseEnd_677969 : Nat := 348123965848163176869583

theorem tailTrace_677969 : CollatzResearch.WordTrace tailWord_677969 prefixEnd_677969 348123965848163176869583 := by
  unfold tailWord_677969
  simp only [CollatzResearch.WordTrace]
  refine ⟨24727560880841575731964961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16485040587227717154643307 24727560880841575731964961)
  ·
    refine ⟨18545670660631181798973721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24727560880841575731964961 18545670660631181798973721)
    ·
      refine ⟨13909252995473386349230291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18545670660631181798973721 13909252995473386349230291)
      ·
        refine ⟨20863879493210079523845437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13909252995473386349230291 20863879493210079523845437)
        ·
          refine ⟨7823954809953779821442039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20863879493210079523845437 7823954809953779821442039)
          ·
            refine ⟨11735932214930669732163059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7823954809953779821442039 11735932214930669732163059)
            ·
              refine ⟨17603898322396004598244589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11735932214930669732163059 17603898322396004598244589)
              ·
                refine ⟨6601461870898501724341721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17603898322396004598244589 6601461870898501724341721)
                ·
                  refine ⟨4951096403173876293256291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601461870898501724341721 4951096403173876293256291)
                  ·
                    refine ⟨7426644604760814439884437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4951096403173876293256291 7426644604760814439884437)
                    ·
                      refine ⟨348123965848163176869583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7426644604760814439884437 348123965848163176869583)
                      ·
                        rfl

theorem cell23_677969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_677969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677969 prefixEnd_677969 := by exact prefixLift 677969
  have htrace : WordTrace (prefixWord ++ tailWord_677969) baseStart_677969 baseEnd_677969 := by
    simpa [prefixWord, tailWord_677969, baseEnd_677969] using wordTrace_append hprefix tailTrace_677969
  have hstable : (prefixWord ++ tailWord_677969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677969).length < 2 ^ (prefixWord ++ tailWord_677969).sum := by decide
  have hdescent : baseEnd_677969 < baseStart_677969 := by decide
  rcases family_descends (prefixWord ++ tailWord_677969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677974 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_677974 : Nat := 118140960795 + 677974 * 2 ^ 59
def prefixEnd_677974 : Nat := 4983230072969 + 3 ^ 40 * 677974 * 2
def baseEnd_677974 : Nat := 38680725916826184145229

theorem tailTrace_677974 : CollatzResearch.WordTrace tailWord_677974 prefixEnd_677974 38680725916826184145229 := by
  unfold tailWord_677974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545483952863966349118561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16485162163882307723931317 1545483952863966349118561)
  ·
    refine ⟨1159112964647974761838921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1545483952863966349118561 1159112964647974761838921)
    ·
      refine ⟨869334723485981071379191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1159112964647974761838921 869334723485981071379191)
      ·
        refine ⟨1304002085228971607068787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869334723485981071379191 1304002085228971607068787)
        ·
          refine ⟨1956003127843457410603181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304002085228971607068787 1956003127843457410603181)
          ·
            refine ⟨733501172941296528976193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956003127843457410603181 733501172941296528976193)
            ·
              refine ⟨550125879705972396732145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733501172941296528976193 550125879705972396732145)
              ·
                refine ⟨412594409779479297549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550125879705972396732145 412594409779479297549109)
                ·
                  refine ⟨38680725916826184145229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 412594409779479297549109 38680725916826184145229)
                  ·
                    rfl

theorem cell23_677974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_677974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677974 prefixEnd_677974 := by exact prefixLift 677974
  have htrace : WordTrace (prefixWord ++ tailWord_677974) baseStart_677974 baseEnd_677974 := by
    simpa [prefixWord, tailWord_677974, baseEnd_677974] using wordTrace_append hprefix tailTrace_677974
  have hstable : (prefixWord ++ tailWord_677974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677974).length < 2 ^ (prefixWord ++ tailWord_677974).sum := by decide
  have hdescent : baseEnd_677974 < baseStart_677974 := by decide
  rcases family_descends (prefixWord ++ tailWord_677974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_677996 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 6]
def baseStart_677996 : Nat := 118140960795 + 677996 * 2 ^ 59
def prefixEnd_677996 : Nat := 4983230072969 + 3 ^ 40 * 677996 * 2
def baseEnd_677996 : Nat := 38681981091759396803551

theorem tailTrace_677996 : CollatzResearch.WordTrace tailWord_677996 prefixEnd_677996 38681981091759396803551 := by
  unfold tailWord_677996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12364272825871879671598921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16485697101162506228798561 12364272825871879671598921)
  ·
    refine ⟨9273204619403909753699191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12364272825871879671598921 9273204619403909753699191)
    ·
      refine ⟨13909806929105864630548787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9273204619403909753699191 13909806929105864630548787)
      ·
        refine ⟨20864710393658796945823181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13909806929105864630548787 20864710393658796945823181)
        ·
          refine ⟨7824266397622048854683693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20864710393658796945823181 7824266397622048854683693)
          ·
            refine ⟨2934099899108268320506385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7824266397622048854683693 2934099899108268320506385)
            ·
              refine ⟨2200574924331201240379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934099899108268320506385 2200574924331201240379789)
              ·
                refine ⟨825215596624200465142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2200574924331201240379789 825215596624200465142421)
                ·
                  refine ⟨38681981091759396803551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 825215596624200465142421 38681981091759396803551)
                  ·
                    rfl

theorem cell23_677996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_677996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_677996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_677996 prefixEnd_677996 := by exact prefixLift 677996
  have htrace : WordTrace (prefixWord ++ tailWord_677996) baseStart_677996 baseEnd_677996 := by
    simpa [prefixWord, tailWord_677996, baseEnd_677996] using wordTrace_append hprefix tailTrace_677996
  have hstable : (prefixWord ++ tailWord_677996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_677996).length < 2 ^ (prefixWord ++ tailWord_677996).sum := by decide
  have hdescent : baseEnd_677996 < baseStart_677996 := by decide
  rcases family_descends (prefixWord ++ tailWord_677996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678017 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 1, 4]
def baseStart_678017 : Nat := 118140960795 + 678017 * 2 ^ 59
def prefixEnd_678017 : Nat := 4983230072969 + 3 ^ 40 * 678017 * 2
def baseEnd_678017 : Nat := 116049537639859663023121

theorem tailTrace_678017 : CollatzResearch.WordTrace tailWord_678017 prefixEnd_678017 116049537639859663023121 := by
  unfold tailWord_678017
  simp only [CollatzResearch.WordTrace]
  refine ⟨24729311584667679929712305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16486207723111786619808203 24729311584667679929712305)
  ·
    refine ⟨18546983688500759947284229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24729311584667679929712305 18546983688500759947284229)
    ·
      refine ⟨3477559441593892490115793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18546983688500759947284229 3477559441593892490115793)
      ·
        refine ⟨2608169581195419367586845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477559441593892490115793 2608169581195419367586845)
        ·
          refine ⟨978063592948282262845067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2608169581195419367586845 978063592948282262845067)
          ·
            refine ⟨1467095389422423394267601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978063592948282262845067 1467095389422423394267601)
            ·
              refine ⟨1100321542066817545700701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467095389422423394267601 1100321542066817545700701)
              ·
                refine ⟨412620578275056579637763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100321542066817545700701 412620578275056579637763)
                ·
                  refine ⟨618930867412584869456645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412620578275056579637763 618930867412584869456645)
                  ·
                    refine ⟨116049537639859663023121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618930867412584869456645 116049537639859663023121)
                    ·
                      rfl

theorem cell23_678017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_678017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678017 prefixEnd_678017 := by exact prefixLift 678017
  have htrace : WordTrace (prefixWord ++ tailWord_678017) baseStart_678017 baseEnd_678017 := by
    simpa [prefixWord, tailWord_678017, baseEnd_678017] using wordTrace_append hprefix tailTrace_678017
  have hstable : (prefixWord ++ tailWord_678017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678017).length < 2 ^ (prefixWord ++ tailWord_678017).sum := by decide
  have hdescent : baseEnd_678017 < baseStart_678017 := by decide
  rcases family_descends (prefixWord ++ tailWord_678017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678030 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_678030 : Nat := 118140960795 + 678030 * 2 ^ 59
def prefixEnd_678030 : Nat := 4983230072969 + 3 ^ 40 * 678030 * 2
def baseEnd_678030 : Nat := 38683920907565270911867

theorem tailTrace_678030 : CollatzResearch.WordTrace tailWord_678030 prefixEnd_678030 38683920907565270911867 := by
  unfold tailWord_678030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091223216702572893741943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16486523822413722099957029 3091223216702572893741943)
  ·
    refine ⟨4636834825053859340612915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091223216702572893741943 4636834825053859340612915)
    ·
      refine ⟨6955252237580789010919373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636834825053859340612915 6955252237580789010919373)
      ·
        refine ⟨2608219589092795879094765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6955252237580789010919373 2608219589092795879094765)
        ·
          refine ⟨978082345909798454660537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2608219589092795879094765 978082345909798454660537)
          ·
            refine ⟨733561759432348840995403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978082345909798454660537 733561759432348840995403)
            ·
              refine ⟨1100342639148523261493105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733561759432348840995403 1100342639148523261493105)
              ·
                refine ⟨825256979361392446119829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100342639148523261493105 825256979361392446119829)
                ·
                  refine ⟨38683920907565270911867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 825256979361392446119829 38683920907565270911867)
                  ·
                    rfl

theorem cell23_678030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_678030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678030 prefixEnd_678030 := by exact prefixLift 678030
  have htrace : WordTrace (prefixWord ++ tailWord_678030) baseStart_678030 baseEnd_678030 := by
    simpa [prefixWord, tailWord_678030, baseEnd_678030] using wordTrace_append hprefix tailTrace_678030
  have hstable : (prefixWord ++ tailWord_678030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678030).length < 2 ^ (prefixWord ++ tailWord_678030).sum := by decide
  have hdescent : baseEnd_678030 < baseStart_678030 := by decide
  rcases family_descends (prefixWord ++ tailWord_678030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678050 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_678050 : Nat := 118140960795 + 678050 * 2 ^ 59
def prefixEnd_678050 : Nat := 4983230072969 + 3 ^ 40 * 678050 * 2
def baseEnd_678050 : Nat := 348165557781177359956711

theorem tailTrace_678050 : CollatzResearch.WordTrace tailWord_678050 prefixEnd_678050 348165557781177359956711 := by
  unfold tailWord_678050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182628798387031641415901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16487010129032084377109069 6182628798387031641415901)
  ·
    refine ⟨2318485799395136865530963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6182628798387031641415901 2318485799395136865530963)
    ·
      refine ⟨3477728699092705298296445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318485799395136865530963 3477728699092705298296445)
      ·
        refine ⟨1304148262159764486861167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3477728699092705298296445 1304148262159764486861167)
        ·
          refine ⟨1956222393239646730291751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304148262159764486861167 1956222393239646730291751)
          ·
            refine ⟨2934333589859470095437627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956222393239646730291751 2934333589859470095437627)
            ·
              refine ⟨4401500384789205143156441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934333589859470095437627 4401500384789205143156441)
              ·
                refine ⟨3301125288591903857367331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401500384789205143156441 3301125288591903857367331)
                ·
                  refine ⟨4951687932887855786050997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301125288591903857367331 4951687932887855786050997)
                  ·
                    refine ⟨464220743708236479942281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4951687932887855786050997 464220743708236479942281)
                    ·
                      refine ⟨348165557781177359956711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464220743708236479942281 348165557781177359956711)
                      ·
                        rfl

theorem cell23_678050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_678050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678050 prefixEnd_678050 := by exact prefixLift 678050
  have htrace : WordTrace (prefixWord ++ tailWord_678050) baseStart_678050 baseEnd_678050 := by
    simpa [prefixWord, tailWord_678050, baseEnd_678050] using wordTrace_append hprefix tailTrace_678050
  have hstable : (prefixWord ++ tailWord_678050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678050).length < 2 ^ (prefixWord ++ tailWord_678050).sum := by decide
  have hdescent : baseEnd_678050 < baseStart_678050 := by decide
  rcases family_descends (prefixWord ++ tailWord_678050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678066 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_678066 : Nat := 118140960795 + 678066 * 2 ^ 59
def prefixEnd_678066 : Nat := 4983230072969 + 3 ^ 40 * 678066 * 2
def baseEnd_678066 : Nat := 348173773471649297356637

theorem tailTrace_678066 : CollatzResearch.WordTrace tailWord_678066 prefixEnd_678066 348173773471649297356637 := by
  unfold tailWord_678066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182774690372540324561513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16487399174326774198830701 6182774690372540324561513)
  ·
    refine ⟨4637081017779405243421135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6182774690372540324561513 4637081017779405243421135)
    ·
      refine ⟨6955621526669107865131703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637081017779405243421135 6955621526669107865131703)
      ·
        refine ⟨10433432290003661797697555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6955621526669107865131703 10433432290003661797697555)
        ·
          refine ⟨15650148435005492696546333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433432290003661797697555 15650148435005492696546333)
          ·
            refine ⟨5868805663127059761204875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15650148435005492696546333 5868805663127059761204875)
            ·
              refine ⟨8803208494690589641807313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868805663127059761204875 8803208494690589641807313)
              ·
                refine ⟨6602406371017942231355485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8803208494690589641807313 6602406371017942231355485)
                ·
                  refine ⟨2475902389131728336758307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6602406371017942231355485 2475902389131728336758307)
                  ·
                    refine ⟨3713853583697592505137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2475902389131728336758307 3713853583697592505137461)
                    ·
                      refine ⟨348173773471649297356637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3713853583697592505137461 348173773471649297356637)
                      ·
                        rfl

theorem cell23_678066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_678066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678066 prefixEnd_678066 := by exact prefixLift 678066
  have htrace : WordTrace (prefixWord ++ tailWord_678066) baseStart_678066 baseEnd_678066 := by
    simpa [prefixWord, tailWord_678066, baseEnd_678066] using wordTrace_append hprefix tailTrace_678066
  have hstable : (prefixWord ++ tailWord_678066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678066).length < 2 ^ (prefixWord ++ tailWord_678066).sum := by decide
  have hdescent : baseEnd_678066 < baseStart_678066 := by decide
  rcases family_descends (prefixWord ++ tailWord_678066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678068 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_678068 : Nat := 118140960795 + 678068 * 2 ^ 59
def prefixEnd_678068 : Nat := 4983230072969 + 3 ^ 40 * 678068 * 2
def baseEnd_678068 : Nat := 116058266810986096510543

theorem tailTrace_678068 : CollatzResearch.WordTrace tailWord_678068 prefixEnd_678068 116058266810986096510543 := by
  unfold tailWord_678068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12365585853741457819909429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16487447804988610426545905 12365585853741457819909429)
  ·
    refine ⟨1159273673788261670616509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12365585853741457819909429 1159273673788261670616509)
    ·
      refine ⟨434727627670598126481191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1159273673788261670616509 434727627670598126481191)
      ·
        refine ⟨652091441505897189721787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434727627670598126481191 652091441505897189721787)
        ·
          refine ⟨978137162258845784582681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652091441505897189721787 978137162258845784582681)
          ·
            refine ⟨733602871694134338437011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978137162258845784582681 733602871694134338437011)
            ·
              refine ⟨1100404307541201507655517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733602871694134338437011 1100404307541201507655517)
              ·
                refine ⟨412651615327950565370819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1100404307541201507655517 412651615327950565370819)
                ·
                  refine ⟨618977422991925848056229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412651615327950565370819 618977422991925848056229)
                  ·
                    refine ⟨116058266810986096510543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618977422991925848056229 116058266810986096510543)
                    ·
                      rfl

theorem cell23_678068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_678068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678068 prefixEnd_678068 := by exact prefixLift 678068
  have htrace : WordTrace (prefixWord ++ tailWord_678068) baseStart_678068 baseEnd_678068 := by
    simpa [prefixWord, tailWord_678068, baseEnd_678068] using wordTrace_append hprefix tailTrace_678068
  have hstable : (prefixWord ++ tailWord_678068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678068).length < 2 ^ (prefixWord ++ tailWord_678068).sum := by decide
  have hdescent : baseEnd_678068 < baseStart_678068 := by decide
  rcases family_descends (prefixWord ++ tailWord_678068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678097 : List Nat := [1, 2, 2, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_678097 : Nat := 118140960795 + 678097 * 2 ^ 59
def prefixEnd_678097 : Nat := 4983230072969 + 3 ^ 40 * 678097 * 2
def baseEnd_678097 : Nat := 348189691371938676068995

theorem tailTrace_678097 : CollatzResearch.WordTrace tailWord_678097 prefixEnd_678097 348189691371938676068995 := by
  unfold tailWord_678097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732229424377853592624545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16488152949585235728416363 24732229424377853592624545)
  ·
    refine ⟨18549172068283390194468409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24732229424377853592624545 18549172068283390194468409)
    ·
      refine ⟨13911879051212542645851307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18549172068283390194468409 13911879051212542645851307)
      ·
        refine ⟨20867818576818813968776961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13911879051212542645851307 20867818576818813968776961)
        ·
          refine ⟨15650863932614110476582721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20867818576818813968776961 15650863932614110476582721)
          ·
            refine ⟨11738147949460582857437041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15650863932614110476582721 11738147949460582857437041)
            ·
              refine ⟨8803610962095437143077781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11738147949460582857437041 8803610962095437143077781)
              ·
                refine ⟨412669263848223616081771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8803610962095437143077781 412669263848223616081771)
                ·
                  refine ⟨619003895772335424122657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412669263848223616081771 619003895772335424122657)
                  ·
                    refine ⟨464252921829251568091993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619003895772335424122657 464252921829251568091993)
                    ·
                      refine ⟨348189691371938676068995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464252921829251568091993 348189691371938676068995)
                      ·
                        rfl

theorem cell23_678097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_678097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678097 prefixEnd_678097 := by exact prefixLift 678097
  have htrace : WordTrace (prefixWord ++ tailWord_678097) baseStart_678097 baseEnd_678097 := by
    simpa [prefixWord, tailWord_678097, baseEnd_678097] using wordTrace_append hprefix tailTrace_678097
  have hstable : (prefixWord ++ tailWord_678097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678097).length < 2 ^ (prefixWord ++ tailWord_678097).sum := by decide
  have hdescent : baseEnd_678097 < baseStart_678097 := by decide
  rcases family_descends (prefixWord ++ tailWord_678097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678113 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_678113 : Nat := 118140960795 + 678113 * 2 ^ 59
def prefixEnd_678113 : Nat := 4983230072969 + 3 ^ 40 * 678113 * 2
def baseEnd_678113 : Nat := 348197907062410613468921

theorem tailTrace_678113 : CollatzResearch.WordTrace tailWord_678113 prefixEnd_678113 348197907062410613468921 := by
  unfold tailWord_678113
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732812992319888325206993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16488541994879925550137995 24732812992319888325206993)
  ·
    refine ⟨18549609744239916243905245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24732812992319888325206993 18549609744239916243905245)
    ·
      refine ⟨6956103654089968591464467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18549609744239916243905245 6956103654089968591464467)
      ·
        refine ⟨10434155481134952887196701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956103654089968591464467 10434155481134952887196701)
        ·
          refine ⟨3912808305425607332698763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10434155481134952887196701 3912808305425607332698763)
          ·
            refine ⟨5869212458138410999048145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912808305425607332698763 5869212458138410999048145)
            ·
              refine ⟨4401909343603808249286109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869212458138410999048145 4401909343603808249286109)
              ·
                refine ⟨1650716003851428093482291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4401909343603808249286109 1650716003851428093482291)
                ·
                  refine ⟨2476074005777142140223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650716003851428093482291 2476074005777142140223437)
                  ·
                    refine ⟨928527752166428302583789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476074005777142140223437 928527752166428302583789)
                    ·
                      refine ⟨348197907062410613468921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928527752166428302583789 348197907062410613468921)
                      ·
                        rfl

theorem cell23_678113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_678113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678113 prefixEnd_678113 := by exact prefixLift 678113
  have htrace : WordTrace (prefixWord ++ tailWord_678113) baseStart_678113 baseEnd_678113 := by
    simpa [prefixWord, tailWord_678113, baseEnd_678113] using wordTrace_append hprefix tailTrace_678113
  have hstable : (prefixWord ++ tailWord_678113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678113).length < 2 ^ (prefixWord ++ tailWord_678113).sum := by decide
  have hdescent : baseEnd_678113 < baseStart_678113 := by decide
  rcases family_descends (prefixWord ++ tailWord_678113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678114 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_678114 : Nat := 118140960795 + 678114 * 2 ^ 59
def prefixEnd_678114 : Nat := 4983230072969 + 3 ^ 40 * 678114 * 2
def baseEnd_678114 : Nat := 348198420543065109556417

theorem tailTrace_678114 : CollatzResearch.WordTrace tailWord_678114 prefixEnd_678114 348198420543065109556417 := by
  unfold tailWord_678114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183212366329066373998349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16488566310210843663995597 6183212366329066373998349)
  ·
    refine ⟨2318704637373399890249381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6183212366329066373998349 2318704637373399890249381)
    ·
      refine ⟨434757119507512479421759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2318704637373399890249381 434757119507512479421759)
      ·
        refine ⟨652135679261268719132639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434757119507512479421759 652135679261268719132639)
        ·
          refine ⟨978203518891903078698959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652135679261268719132639 978203518891903078698959)
          ·
            refine ⟨1467305278337854618048439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978203518891903078698959 1467305278337854618048439)
            ·
              refine ⟨2200957917506781927072659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467305278337854618048439 2200957917506781927072659)
              ·
                refine ⟨3301436876260172890608989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200957917506781927072659 3301436876260172890608989)
                ·
                  refine ⟨1238038828597564833978371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3301436876260172890608989 1238038828597564833978371)
                  ·
                    refine ⟨1857058242896347250967557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238038828597564833978371 1857058242896347250967557)
                    ·
                      refine ⟨348198420543065109556417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1857058242896347250967557 348198420543065109556417)
                      ·
                        rfl

theorem cell23_678114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_678114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678114 prefixEnd_678114 := by exact prefixLift 678114
  have htrace : WordTrace (prefixWord ++ tailWord_678114) baseStart_678114 baseEnd_678114 := by
    simpa [prefixWord, tailWord_678114, baseEnd_678114] using wordTrace_append hprefix tailTrace_678114
  have hstable : (prefixWord ++ tailWord_678114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678114).length < 2 ^ (prefixWord ++ tailWord_678114).sum := by decide
  have hdescent : baseEnd_678114 < baseStart_678114 := by decide
  rcases family_descends (prefixWord ++ tailWord_678114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678117 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_678117 : Nat := 118140960795 + 678117 * 2 ^ 59
def prefixEnd_678117 : Nat := 4983230072969 + 3 ^ 40 * 678117 * 2
def baseEnd_678117 : Nat := 348199960985028597818903

theorem tailTrace_678117 : CollatzResearch.WordTrace tailWord_678117 prefixEnd_678117 348199960985028597818903 := by
  unfold tailWord_678117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24732958884305397008352605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16488639256203598005568403 24732958884305397008352605)
  ·
    refine ⟨9274859581614523878132227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24732958884305397008352605 9274859581614523878132227)
    ·
      refine ⟨13912289372421785817198341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9274859581614523878132227 13912289372421785817198341)
      ·
        refine ⟨2608554257329084840724689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13912289372421785817198341 2608554257329084840724689)
        ·
          refine ⟨1956415692996813630543517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608554257329084840724689 1956415692996813630543517)
          ·
            refine ⟨733655884873805111453819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1956415692996813630543517 733655884873805111453819)
            ·
              refine ⟨1100483827310707667180729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733655884873805111453819 1100483827310707667180729)
              ·
                refine ⟨825362870483030750385547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100483827310707667180729 825362870483030750385547)
                ·
                  refine ⟨1238044305724546125578321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825362870483030750385547 1238044305724546125578321)
                  ·
                    refine ⟨928533229293409594183741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238044305724546125578321 928533229293409594183741)
                    ·
                      refine ⟨348199960985028597818903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928533229293409594183741 348199960985028597818903)
                      ·
                        rfl

theorem cell23_678117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_678117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678117 prefixEnd_678117 := by exact prefixLift 678117
  have htrace : WordTrace (prefixWord ++ tailWord_678117) baseStart_678117 baseEnd_678117 := by
    simpa [prefixWord, tailWord_678117, baseEnd_678117] using wordTrace_append hprefix tailTrace_678117
  have hstable : (prefixWord ++ tailWord_678117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678117).length < 2 ^ (prefixWord ++ tailWord_678117).sum := by decide
  have hdescent : baseEnd_678117 < baseStart_678117 := by decide
  rcases family_descends (prefixWord ++ tailWord_678117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678130 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_678130 : Nat := 118140960795 + 678130 * 2 ^ 59
def prefixEnd_678130 : Nat := 4983230072969 + 3 ^ 40 * 678130 * 2
def baseEnd_678130 : Nat := 348206636233537046956343

theorem tailTrace_678130 : CollatzResearch.WordTrace tailWord_678130 prefixEnd_678130 348206636233537046956343 := by
  unfold tailWord_678130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183358258314575057143961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16488955355505533485717229 6183358258314575057143961)
  ·
    refine ⟨4637518693735931292857971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6183358258314575057143961 4637518693735931292857971)
    ·
      refine ⟨6956278040603896939286957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637518693735931292857971 6956278040603896939286957)
      ·
        refine ⟨2608604265226461352232609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6956278040603896939286957 2608604265226461352232609)
        ·
          refine ⟨1956453198919846014174457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608604265226461352232609 1956453198919846014174457)
          ·
            refine ⟨1467339899189884510630843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956453198919846014174457 1467339899189884510630843)
            ·
              refine ⟨2201009848784826765946265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467339899189884510630843 2201009848784826765946265)
              ·
                refine ⟨1650757386588620074459699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201009848784826765946265 1650757386588620074459699)
                ·
                  refine ⟨2476136079882930111689549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650757386588620074459699 2476136079882930111689549)
                  ·
                    refine ⟨928551029956098791883581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476136079882930111689549 928551029956098791883581)
                    ·
                      refine ⟨348206636233537046956343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928551029956098791883581 348206636233537046956343)
                      ·
                        rfl

theorem cell23_678130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_678130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678130 prefixEnd_678130 := by exact prefixLift 678130
  have htrace : WordTrace (prefixWord ++ tailWord_678130) baseStart_678130 baseEnd_678130 := by
    simpa [prefixWord, tailWord_678130, baseEnd_678130] using wordTrace_append hprefix tailTrace_678130
  have hstable : (prefixWord ++ tailWord_678130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678130).length < 2 ^ (prefixWord ++ tailWord_678130).sum := by decide
  have hdescent : baseEnd_678130 < baseStart_678130 := by decide
  rcases family_descends (prefixWord ++ tailWord_678130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678136 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_678136 : Nat := 118140960795 + 678136 * 2 ^ 59
def prefixEnd_678136 : Nat := 4983230072969 + 3 ^ 40 * 678136 * 2
def baseEnd_678136 : Nat := 348209717117464023481315

theorem tailTrace_678136 : CollatzResearch.WordTrace tailWord_678136 prefixEnd_678136 348209717117464023481315 := by
  unfold tailWord_678136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12366825935618281626647131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16489101247491042168862841 12366825935618281626647131)
  ·
    refine ⟨18550238903427422439970697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12366825935618281626647131 18550238903427422439970697)
    ·
      refine ⟨13912679177570566829978023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18550238903427422439970697 13912679177570566829978023)
      ·
        refine ⟨20869018766355850244967035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13912679177570566829978023 20869018766355850244967035)
        ·
          refine ⟨31303528149533775367450553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20869018766355850244967035 31303528149533775367450553)
          ·
            refine ⟨23477646112150331525587915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31303528149533775367450553 23477646112150331525587915)
            ·
              refine ⟨35216469168225497288381873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23477646112150331525587915 35216469168225497288381873)
              ·
                refine ⟨26412351876169122966286405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35216469168225497288381873 26412351876169122966286405)
                ·
                  refine ⟨4952315976781710556178701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26412351876169122966286405 4952315976781710556178701)
                  ·
                    refine ⟨1857118491293141458567013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4952315976781710556178701 1857118491293141458567013)
                    ·
                      refine ⟨348209717117464023481315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1857118491293141458567013 348209717117464023481315)
                      ·
                        rfl

theorem cell23_678136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_678136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678136 prefixEnd_678136 := by exact prefixLift 678136
  have htrace : WordTrace (prefixWord ++ tailWord_678136) baseStart_678136 baseEnd_678136 := by
    simpa [prefixWord, tailWord_678136, baseEnd_678136] using wordTrace_append hprefix tailTrace_678136
  have hstable : (prefixWord ++ tailWord_678136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678136).length < 2 ^ (prefixWord ++ tailWord_678136).sum := by decide
  have hdescent : baseEnd_678136 < baseStart_678136 := by decide
  rcases family_descends (prefixWord ++ tailWord_678136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678148 : List Nat := [2, 3, 2, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_678148 : Nat := 118140960795 + 678148 * 2 ^ 59
def prefixEnd_678148 : Nat := 4983230072969 + 3 ^ 40 * 678148 * 2
def baseEnd_678148 : Nat := 348215878885317976531261

theorem tailTrace_678148 : CollatzResearch.WordTrace tailWord_678148 prefixEnd_678148 348215878885317976531261 := by
  unfold tailWord_678148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367044773596544651365549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16489393031462059535154065 12367044773596544651365549)
  ·
    refine ⟨4637641790098704244262081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12367044773596544651365549 4637641790098704244262081)
    ·
      refine ⟨3478231342574028183196561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4637641790098704244262081 3478231342574028183196561)
      ·
        refine ⟨2608673506930521137397421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3478231342574028183196561 2608673506930521137397421)
        ·
          refine ⟨978252565098945426524033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2608673506930521137397421 978252565098945426524033)
          ·
            refine ⟨733689423824209069893025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978252565098945426524033 733689423824209069893025)
            ·
              refine ⟨550267067868156802419769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733689423824209069893025 550267067868156802419769)
              ·
                refine ⟨412700300901117601814827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550267067868156802419769 412700300901117601814827)
                ·
                  refine ⟨619050451351676402722241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412700300901117601814827 619050451351676402722241)
                  ·
                    refine ⟨464287838513757302041681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619050451351676402722241 464287838513757302041681)
                    ·
                      refine ⟨348215878885317976531261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464287838513757302041681 348215878885317976531261)
                      ·
                        rfl

theorem cell23_678148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_678148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678148 prefixEnd_678148 := by exact prefixLift 678148
  have htrace : WordTrace (prefixWord ++ tailWord_678148) baseStart_678148 baseEnd_678148 := by
    simpa [prefixWord, tailWord_678148, baseEnd_678148] using wordTrace_append hprefix tailTrace_678148
  have hstable : (prefixWord ++ tailWord_678148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678148).length < 2 ^ (prefixWord ++ tailWord_678148).sum := by decide
  have hdescent : baseEnd_678148 < baseStart_678148 := by decide
  rcases family_descends (prefixWord ++ tailWord_678148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678174 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_678174 : Nat := 118140960795 + 678174 * 2 ^ 59
def prefixEnd_678174 : Nat := 4983230072969 + 3 ^ 40 * 678174 * 2
def baseEnd_678174 : Nat := 348229229382334874806141

theorem tailTrace_678174 : CollatzResearch.WordTrace tailWord_678174 prefixEnd_678174 348229229382334874806141 := by
  unfold tailWord_678174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091879730637361967897197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16490025230065930495451717 3091879730637361967897197)
  ·
    refine ⟨1159454898989010737961449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3091879730637361967897197 1159454898989010737961449)
    ·
      refine ⟨869591174241758053471087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1159454898989010737961449 869591174241758053471087)
      ·
        refine ⟨1304386761362637080206631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869591174241758053471087 1304386761362637080206631)
        ·
          refine ⟨1956580142043955620309947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304386761362637080206631 1956580142043955620309947)
          ·
            refine ⟨2934870213065933430464921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956580142043955620309947 2934870213065933430464921)
            ·
              refine ⟨2201152659799450072848691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934870213065933430464921 2201152659799450072848691)
              ·
                refine ⟨3301728989699175109273037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201152659799450072848691 3301728989699175109273037)
                ·
                  refine ⟨1238148371137190665977389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3301728989699175109273037 1238148371137190665977389)
                  ·
                    refine ⟨464305639176446499741521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238148371137190665977389 464305639176446499741521)
                    ·
                      refine ⟨348229229382334874806141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464305639176446499741521 348229229382334874806141)
                      ·
                        rfl

theorem cell23_678174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_678174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678174 prefixEnd_678174 := by exact prefixLift 678174
  have htrace : WordTrace (prefixWord ++ tailWord_678174) baseStart_678174 baseEnd_678174 := by
    simpa [prefixWord, tailWord_678174, baseEnd_678174] using wordTrace_append hprefix tailTrace_678174
  have hstable : (prefixWord ++ tailWord_678174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678174).length < 2 ^ (prefixWord ++ tailWord_678174).sum := by decide
  have hdescent : baseEnd_678174 < baseStart_678174 := by decide
  rcases family_descends (prefixWord ++ tailWord_678174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678243 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_678243 : Nat := 118140960795 + 678243 * 2 ^ 59
def prefixEnd_678243 : Nat := 4983230072969 + 3 ^ 40 * 678243 * 2
def baseEnd_678243 : Nat := 348264659547495104843323

theorem tailTrace_678243 : CollatzResearch.WordTrace tailWord_678243 prefixEnd_678243 348264659547495104843323 := by
  unfold tailWord_678243
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737554481848920527439383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16491702987899280351626255 24737554481848920527439383)
  ·
    refine ⟨37106331722773380791159075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24737554481848920527439383 37106331722773380791159075)
    ·
      refine ⟨55659497584160071186738613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37106331722773380791159075 55659497584160071186738613)
      ·
        refine ⟨5218077898515006673756745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55659497584160071186738613 5218077898515006673756745)
        ·
          refine ⟨3913558423886255005317559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5218077898515006673756745 3913558423886255005317559)
          ·
            refine ⟨5870337635829382507976339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913558423886255005317559 5870337635829382507976339)
            ·
              refine ⟨8805506453744073761964509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870337635829382507976339 8805506453744073761964509)
              ·
                refine ⟨3302064920154027660736691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8805506453744073761964509 3302064920154027660736691)
                ·
                  refine ⟨4953097380231041491105037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302064920154027660736691 4953097380231041491105037)
                  ·
                    refine ⟨1857411517586640559164389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4953097380231041491105037 1857411517586640559164389)
                    ·
                      refine ⟨348264659547495104843323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1857411517586640559164389 348264659547495104843323)
                      ·
                        rfl

theorem cell23_678243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_678243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678243 prefixEnd_678243 := by exact prefixLift 678243
  have htrace : WordTrace (prefixWord ++ tailWord_678243) baseStart_678243 baseEnd_678243 := by
    simpa [prefixWord, tailWord_678243, baseEnd_678243] using wordTrace_append hprefix tailTrace_678243
  have hstable : (prefixWord ++ tailWord_678243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678243).length < 2 ^ (prefixWord ++ tailWord_678243).sum := by decide
  have hdescent : baseEnd_678243 < baseStart_678243 := by decide
  rcases family_descends (prefixWord ++ tailWord_678243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_678263 : Nat := 118140960795 + 678263 * 2 ^ 59
def prefixEnd_678263 : Nat := 4983230072969 + 3 ^ 40 * 678263 * 2
def baseEnd_678263 : Nat := 348274929160585026593231

theorem tailTrace_678263 : CollatzResearch.WordTrace tailWord_678263 prefixEnd_678263 348274929160585026593231 := by
  unfold tailWord_678263
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738283941776463943167443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16492189294517642628778295 24738283941776463943167443)
  ·
    refine ⟨37107425912664695914751165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24738283941776463943167443 37107425912664695914751165)
    ·
      refine ⟨13915284717249260968031687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37107425912664695914751165 13915284717249260968031687)
      ·
        refine ⟨20872927075873891452047531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13915284717249260968031687 20872927075873891452047531)
        ·
          refine ⟨31309390613810837178071297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20872927075873891452047531 31309390613810837178071297)
          ·
            refine ⟨23482042960358127883553473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31309390613810837178071297 23482042960358127883553473)
            ·
              refine ⟨17611532220268595912665105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23482042960358127883553473 17611532220268595912665105)
              ·
                refine ⟨13208649165201446934498829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17611532220268595912665105 13208649165201446934498829)
                ·
                  refine ⟨4953243436950542600437061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13208649165201446934498829 4953243436950542600437061)
                  ·
                    refine ⟨928733144428226737581949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953243436950542600437061 928733144428226737581949)
                    ·
                      refine ⟨348274929160585026593231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928733144428226737581949 348274929160585026593231)
                      ·
                        rfl

theorem cell23_678263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_678263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678263 prefixEnd_678263 := by exact prefixLift 678263
  have htrace : WordTrace (prefixWord ++ tailWord_678263) baseStart_678263 baseEnd_678263 := by
    simpa [prefixWord, tailWord_678263, baseEnd_678263] using wordTrace_append hprefix tailTrace_678263
  have hstable : (prefixWord ++ tailWord_678263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678263).length < 2 ^ (prefixWord ++ tailWord_678263).sum := by decide
  have hdescent : baseEnd_678263 < baseStart_678263 := by decide
  rcases family_descends (prefixWord ++ tailWord_678263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678280 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_678280 : Nat := 118140960795 + 678280 * 2 ^ 59
def prefixEnd_678280 : Nat := 4983230072969 + 3 ^ 40 * 678280 * 2
def baseEnd_678280 : Nat := 348283658331711460080653

theorem tailTrace_678280 : CollatzResearch.WordTrace tailWord_678280 prefixEnd_678280 348283658331711460080653 := by
  unfold tailWord_678280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369451991357437923268147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16492602655143250564357529 12369451991357437923268147)
  ·
    refine ⟨18554177987036156884902221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12369451991357437923268147 18554177987036156884902221)
    ·
      refine ⟨6957816745138558831838333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18554177987036156884902221 6957816745138558831838333)
      ·
        refine ⟨2609181279426959561939375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6957816745138558831838333 2609181279426959561939375)
        ·
          refine ⟨3913771919140439342909063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609181279426959561939375 3913771919140439342909063)
          ·
            refine ⟨5870657878710659014363595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3913771919140439342909063 5870657878710659014363595)
            ·
              refine ⟨8805986818065988521545393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870657878710659014363595 8805986818065988521545393)
              ·
                refine ⟨6604490113549491391159045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8805986818065988521545393 6604490113549491391159045)
                ·
                  refine ⟨1238341896290529635842321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6604490113549491391159045 1238341896290529635842321)
                  ·
                    refine ⟨928756422217897226881741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238341896290529635842321 928756422217897226881741)
                    ·
                      refine ⟨348283658331711460080653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928756422217897226881741 348283658331711460080653)
                      ·
                        rfl

theorem cell23_678280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_678280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678280 prefixEnd_678280 := by exact prefixLift 678280
  have htrace : WordTrace (prefixWord ++ tailWord_678280) baseStart_678280 baseEnd_678280 := by
    simpa [prefixWord, tailWord_678280, baseEnd_678280] using wordTrace_append hprefix tailTrace_678280
  have hstable : (prefixWord ++ tailWord_678280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678280).length < 2 ^ (prefixWord ++ tailWord_678280).sum := by decide
  have hdescent : baseEnd_678280 < baseStart_678280 := by decide
  rcases family_descends (prefixWord ++ tailWord_678280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678321 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 1, 4]
def baseStart_678321 : Nat := 118140960795 + 678321 * 2 ^ 59
def prefixEnd_678321 : Nat := 4983230072969 + 3 ^ 40 * 678321 * 2
def baseEnd_678321 : Nat := 116101570346181933222655

theorem tailTrace_678321 : CollatzResearch.WordTrace tailWord_678321 prefixEnd_678321 116101570346181933222655 := by
  unfold tailWord_678321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740399375566339848778817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16493599583710893232519211 24740399375566339848778817)
  ·
    refine ⟨18555299531674754886584113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24740399375566339848778817 18555299531674754886584113)
    ·
      refine ⟨13916474648756066164938085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18555299531674754886584113 13916474648756066164938085)
      ·
        refine ⟨2609338996641762405925891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13916474648756066164938085 2609338996641762405925891)
        ·
          refine ⟨3914008494962643608888837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609338996641762405925891 3914008494962643608888837)
          ·
            refine ⟨733876592805495676666657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3914008494962643608888837 733876592805495676666657)
            ·
              refine ⟨550407444604121757499993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733876592805495676666657 550407444604121757499993)
              ·
                refine ⟨412805583453091318124995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550407444604121757499993 412805583453091318124995)
                ·
                  refine ⟨619208375179636977187493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412805583453091318124995 619208375179636977187493)
                  ·
                    refine ⟨116101570346181933222655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 619208375179636977187493 116101570346181933222655)
                    ·
                      rfl

theorem cell23_678321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_678321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678321 prefixEnd_678321 := by exact prefixLift 678321
  have htrace : WordTrace (prefixWord ++ tailWord_678321) baseStart_678321 baseEnd_678321 := by
    simpa [prefixWord, tailWord_678321, baseEnd_678321] using wordTrace_append hprefix tailTrace_678321
  have hstable : (prefixWord ++ tailWord_678321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678321).length < 2 ^ (prefixWord ++ tailWord_678321).sum := by decide
  have hdescent : baseEnd_678321 < baseStart_678321 := by decide
  rcases family_descends (prefixWord ++ tailWord_678321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678360 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_678360 : Nat := 118140960795 + 678360 * 2 ^ 59
def prefixEnd_678360 : Nat := 4983230072969 + 3 ^ 40 * 678360 * 2
def baseEnd_678360 : Nat := 116108245594690382360095

theorem tailTrace_678360 : CollatzResearch.WordTrace tailWord_678360 prefixEnd_678360 116108245594690382360095 := by
  unfold tailWord_678360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12370910911212524754724267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16494547881616699672965689 12370910911212524754724267)
  ·
    refine ⟨18556366366818787132086401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12370910911212524754724267 18556366366818787132086401)
    ·
      refine ⟨13917274775114090349064801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18556366366818787132086401 13917274775114090349064801)
      ·
        refine ⟨10437956081335567761798601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13917274775114090349064801 10437956081335567761798601)
        ·
          refine ⟨7828467061001675821348951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10437956081335567761798601 7828467061001675821348951)
          ·
            refine ⟨11742700591502513732023427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828467061001675821348951 11742700591502513732023427)
            ·
              refine ⟨17614050887253770598035141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742700591502513732023427 17614050887253770598035141)
              ·
                refine ⟨3302634541360081987131589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17614050887253770598035141 3302634541360081987131589)
                ·
                  refine ⟨619243976505015372587173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3302634541360081987131589 619243976505015372587173)
                  ·
                    refine ⟨116108245594690382360095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 619243976505015372587173 116108245594690382360095)
                    ·
                      rfl

theorem cell23_678360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_678360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678360 prefixEnd_678360 := by exact prefixLift 678360
  have htrace : WordTrace (prefixWord ++ tailWord_678360) baseStart_678360 baseEnd_678360 := by
    simpa [prefixWord, tailWord_678360, baseEnd_678360] using wordTrace_append hprefix tailTrace_678360
  have hstable : (prefixWord ++ tailWord_678360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678360).length < 2 ^ (prefixWord ++ tailWord_678360).sum := by decide
  have hdescent : baseEnd_678360 < baseStart_678360 := by decide
  rcases family_descends (prefixWord ++ tailWord_678360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678367 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_678367 : Nat := 118140960795 + 678367 * 2 ^ 59
def prefixEnd_678367 : Nat := 4983230072969 + 3 ^ 40 * 678367 * 2
def baseEnd_678367 : Nat := 348328331148652619692753

theorem tailTrace_678367 : CollatzResearch.WordTrace tailWord_678367 prefixEnd_678367 348328331148652619692753 := by
  unfold tailWord_678367
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742077133399689704953355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16494718088933126469968903 24742077133399689704953355)
  ·
    refine ⟨37113115700099534557430033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24742077133399689704953355 37113115700099534557430033)
    ·
      refine ⟨27834836775074650918072525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37113115700099534557430033 27834836775074650918072525)
      ·
        refine ⟨10438063790652994094277197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27834836775074650918072525 10438063790652994094277197)
        ·
          refine ⟨3914273921494872785353949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10438063790652994094277197 3914273921494872785353949)
          ·
            refine ⟨1467852720560577294507731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3914273921494872785353949 1467852720560577294507731)
            ·
              refine ⟨2201779080840865941761597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467852720560577294507731 2201779080840865941761597)
              ·
                refine ⟨825667155315324728160599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201779080840865941761597 825667155315324728160599)
                ·
                  refine ⟨1238500732972987092240899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825667155315324728160599 1238500732972987092240899)
                  ·
                    refine ⟨1857751099459480638361349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1238500732972987092240899 1857751099459480638361349)
                    ·
                      refine ⟨348328331148652619692753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1857751099459480638361349 348328331148652619692753)
                      ·
                        rfl

theorem cell23_678367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_678367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678367 prefixEnd_678367 := by exact prefixLift 678367
  have htrace : WordTrace (prefixWord ++ tailWord_678367) baseStart_678367 baseEnd_678367 := by
    simpa [prefixWord, tailWord_678367, baseEnd_678367] using wordTrace_append hprefix tailTrace_678367
  have hstable : (prefixWord ++ tailWord_678367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678367).length < 2 ^ (prefixWord ++ tailWord_678367).sum := by decide
  have hdescent : baseEnd_678367 < baseStart_678367 := by decide
  rcases family_descends (prefixWord ++ tailWord_678367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678383 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_678383 : Nat := 118140960795 + 678383 * 2 ^ 59
def prefixEnd_678383 : Nat := 4983230072969 + 3 ^ 40 * 678383 * 2
def baseEnd_678383 : Nat := 348336546839124557092679

theorem tailTrace_678383 : CollatzResearch.WordTrace tailWord_678383 prefixEnd_678383 348336546839124557092679 := by
  unfold tailWord_678383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742660701341724437535803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16495107134227816291690535 24742660701341724437535803)
  ·
    refine ⟨37113991052012586656303705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24742660701341724437535803 37113991052012586656303705)
    ·
      refine ⟨27835493289009439992227779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37113991052012586656303705 27835493289009439992227779)
      ·
        refine ⟨41753239933514159988341669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27835493289009439992227779 41753239933514159988341669)
        ·
          refine ⟨7828732487533904997814063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41753239933514159988341669 7828732487533904997814063)
          ·
            refine ⟨11743098731300857496721095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828732487533904997814063 11743098731300857496721095)
            ·
              refine ⟨17614648096951286245081643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11743098731300857496721095 17614648096951286245081643)
              ·
                refine ⟨26421972145426929367622465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17614648096951286245081643 26421972145426929367622465)
                ·
                  refine ⟨19816479109070197025716849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26421972145426929367622465 19816479109070197025716849)
                  ·
                    refine ⟨14862359331802647769287637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19816479109070197025716849 14862359331802647769287637)
                    ·
                      refine ⟨348336546839124557092679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14862359331802647769287637 348336546839124557092679)
                      ·
                        rfl

theorem cell23_678383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_678383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678383 prefixEnd_678383 := by exact prefixLift 678383
  have htrace : WordTrace (prefixWord ++ tailWord_678383) baseStart_678383 baseEnd_678383 := by
    simpa [prefixWord, tailWord_678383, baseEnd_678383] using wordTrace_append hprefix tailTrace_678383
  have hstable : (prefixWord ++ tailWord_678383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678383).length < 2 ^ (prefixWord ++ tailWord_678383).sum := by decide
  have hdescent : baseEnd_678383 < baseStart_678383 := by decide
  rcases family_descends (prefixWord ++ tailWord_678383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678384 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2]
def baseStart_678384 : Nat := 118140960795 + 678384 * 2 ^ 59
def prefixEnd_678384 : Nat := 4983230072969 + 3 ^ 40 * 678384 * 2
def baseEnd_678384 : Nat := 348337060319779053180175

theorem tailTrace_678384 : CollatzResearch.WordTrace tailWord_678384 prefixEnd_678384 348337060319779053180175 := by
  unfold tailWord_678384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371348587169050804161103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16495131449558734405548137 12371348587169050804161103)
  ·
    refine ⟨18557022880753576206241655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12371348587169050804161103 18557022880753576206241655)
    ·
      refine ⟨27835534321130364309362483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18557022880753576206241655 27835534321130364309362483)
      ·
        refine ⟨41753301481695546464043725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27835534321130364309362483 41753301481695546464043725)
        ·
          refine ⟨15657488055635829924016397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41753301481695546464043725 15657488055635829924016397)
          ·
            refine ⟨5871558020863436221506149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15657488055635829924016397 5871558020863436221506149)
            ·
              refine ⟨1100917128911894291532403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5871558020863436221506149 1100917128911894291532403)
              ·
                refine ⟨1651375693367841437298605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100917128911894291532403 1651375693367841437298605)
                ·
                  refine ⟨619265885012940538986977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1651375693367841437298605 619265885012940538986977)
                  ·
                    refine ⟨464449413759705404240233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619265885012940538986977 464449413759705404240233)
                    ·
                      refine ⟨348337060319779053180175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464449413759705404240233 348337060319779053180175)
                      ·
                        rfl

theorem cell23_678384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2].length) (baseStart_678384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678384 prefixEnd_678384 := by exact prefixLift 678384
  have htrace : WordTrace (prefixWord ++ tailWord_678384) baseStart_678384 baseEnd_678384 := by
    simpa [prefixWord, tailWord_678384, baseEnd_678384] using wordTrace_append hprefix tailTrace_678384
  have hstable : (prefixWord ++ tailWord_678384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678384).length < 2 ^ (prefixWord ++ tailWord_678384).sum := by decide
  have hdescent : baseEnd_678384 < baseStart_678384 := by decide
  rcases family_descends (prefixWord ++ tailWord_678384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678390 : List Nat := [5, 1, 1, 1, 2, 1, 2, 10]
def baseStart_678390 : Nat := 118140960795 + 678390 * 2 ^ 59
def prefixEnd_678390 : Nat := 4983230072969 + 3 ^ 40 * 678390 * 2
def baseEnd_678390 : Nat := 12901486711248371470561

theorem tailTrace_678390 : CollatzResearch.WordTrace tailWord_678390 prefixEnd_678390 12901486711248371470561 := by
  unfold tailWord_678390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546432250769772789565039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16495277341544243088693749 1546432250769772789565039)
  ·
    refine ⟨2319648376154659184347559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546432250769772789565039 2319648376154659184347559)
    ·
      refine ⟨3479472564231988776521339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319648376154659184347559 3479472564231988776521339)
      ·
        refine ⟨5219208846347983164782009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479472564231988776521339 5219208846347983164782009)
        ·
          refine ⟨3914406634760987373586507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219208846347983164782009 3914406634760987373586507)
          ·
            refine ⟨5871609952141481060379761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914406634760987373586507 5871609952141481060379761)
            ·
              refine ⟨4403707464106110795284821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871609952141481060379761 4403707464106110795284821)
              ·
                refine ⟨12901486711248371470561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4403707464106110795284821 12901486711248371470561)
                ·
                  rfl

theorem cell23_678390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_678390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678390 prefixEnd_678390 := by exact prefixLift 678390
  have htrace : WordTrace (prefixWord ++ tailWord_678390) baseStart_678390 baseEnd_678390 := by
    simpa [prefixWord, tailWord_678390, baseEnd_678390] using wordTrace_append hprefix tailTrace_678390
  have hstable : (prefixWord ++ tailWord_678390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678390).length < 2 ^ (prefixWord ++ tailWord_678390).sum := by decide
  have hdescent : baseEnd_678390 < baseStart_678390 := by decide
  rcases family_descends (prefixWord ++ tailWord_678390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678404 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_678404 : Nat := 118140960795 + 678404 * 2 ^ 59
def prefixEnd_678404 : Nat := 4983230072969 + 3 ^ 40 * 678404 * 2
def baseEnd_678404 : Nat := 348347329932868974930083

theorem tailTrace_678404 : CollatzResearch.WordTrace tailWord_678404 prefixEnd_678404 348347329932868974930083 := by
  unfold tailWord_678404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371713317132822512025133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16495617756177096682700177 12371713317132822512025133)
  ·
    refine ⟨4639392493924808442009425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12371713317132822512025133 4639392493924808442009425)
    ·
      refine ⟨3479544370443606331507069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4639392493924808442009425 3479544370443606331507069)
      ·
        refine ⟨1304829138916352374315151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3479544370443606331507069 1304829138916352374315151)
        ·
          refine ⟨1957243708374528561472727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304829138916352374315151 1957243708374528561472727)
          ·
            refine ⟨2935865562561792842209091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957243708374528561472727 2935865562561792842209091)
            ·
              refine ⟨4403798343842689263313637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935865562561792842209091 4403798343842689263313637)
              ·
                refine ⟨825712189470504236871307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4403798343842689263313637 825712189470504236871307)
                ·
                  refine ⟨1238568284205756355306961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825712189470504236871307 1238568284205756355306961)
                  ·
                    refine ⟨928926213154317266480221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1238568284205756355306961 928926213154317266480221)
                    ·
                      refine ⟨348347329932868974930083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928926213154317266480221 348347329932868974930083)
                      ·
                        rfl

theorem cell23_678404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_678404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678404 prefixEnd_678404 := by exact prefixLift 678404
  have htrace : WordTrace (prefixWord ++ tailWord_678404) baseStart_678404 baseEnd_678404 := by
    simpa [prefixWord, tailWord_678404, baseEnd_678404] using wordTrace_append hprefix tailTrace_678404
  have hstable : (prefixWord ++ tailWord_678404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678404).length < 2 ^ (prefixWord ++ tailWord_678404).sum := by decide
  have hdescent : baseEnd_678404 < baseStart_678404 := by decide
  rcases family_descends (prefixWord ++ tailWord_678404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678434 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_678434 : Nat := 118140960795 + 678434 * 2 ^ 59
def prefixEnd_678434 : Nat := 4983230072969 + 3 ^ 40 * 678434 * 2
def baseEnd_678434 : Nat := 348362734352503857554945

theorem tailTrace_678434 : CollatzResearch.WordTrace tailWord_678434 prefixEnd_678434 348362734352503857554945 := by
  unfold tailWord_678434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186130206039240036910589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16496347216104640098428237 6186130206039240036910589)
  ·
    refine ⟨2319798827264715013841471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6186130206039240036910589 2319798827264715013841471)
    ·
      refine ⟨3479698240897072520762207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319798827264715013841471 3479698240897072520762207)
      ·
        refine ⟨5219547361345608781143311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479698240897072520762207 5219547361345608781143311)
        ·
          refine ⟨7829321042018413171714967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219547361345608781143311 7829321042018413171714967)
          ·
            refine ⟨11743981563027619757572451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829321042018413171714967 11743981563027619757572451)
            ·
              refine ⟨17615972344541429636358677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11743981563027619757572451 17615972344541429636358677)
              ·
                refine ⟨825748703650379514204313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17615972344541429636358677 825748703650379514204313)
                ·
                  refine ⟨619311527737784635653235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825748703650379514204313 619311527737784635653235)
                  ·
                    refine ⟨928967291606676953479853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 619311527737784635653235 928967291606676953479853)
                    ·
                      refine ⟨348362734352503857554945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 928967291606676953479853 348362734352503857554945)
                      ·
                        rfl

theorem cell23_678434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_678434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678434 prefixEnd_678434 := by exact prefixLift 678434
  have htrace : WordTrace (prefixWord ++ tailWord_678434) baseStart_678434 baseEnd_678434 := by
    simpa [prefixWord, tailWord_678434, baseEnd_678434] using wordTrace_append hprefix tailTrace_678434
  have hstable : (prefixWord ++ tailWord_678434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678434).length < 2 ^ (prefixWord ++ tailWord_678434).sum := by decide
  have hdescent : baseEnd_678434 < baseStart_678434 := by decide
  rcases family_descends (prefixWord ++ tailWord_678434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678450 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_678450 : Nat := 118140960795 + 678450 * 2 ^ 59
def prefixEnd_678450 : Nat := 4983230072969 + 3 ^ 40 * 678450 * 2
def baseEnd_678450 : Nat := 116123650014325264984957

theorem tailTrace_678450 : CollatzResearch.WordTrace tailWord_678450 prefixEnd_678450 116123650014325264984957 := by
  unfold tailWord_678450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186276098024748720056201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16496736261399329920149869 6186276098024748720056201)
  ·
    refine ⟨4639707073518561540042151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6186276098024748720056201 4639707073518561540042151)
    ·
      refine ⟨6959560610277842310063227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639707073518561540042151 6959560610277842310063227)
      ·
        refine ⟨10439340915416763465094841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959560610277842310063227 10439340915416763465094841)
        ·
          refine ⟨7829505686562572598821131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10439340915416763465094841 7829505686562572598821131)
          ·
            refine ⟨11744258529843858898231697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829505686562572598821131 11744258529843858898231697)
            ·
              refine ⟨8808193897382894173673773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11744258529843858898231697 8808193897382894173673773)
              ·
                refine ⟨3303072711518585315127665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8808193897382894173673773 3303072711518585315127665)
                ·
                  refine ⟨2477304533638938986345749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303072711518585315127665 2477304533638938986345749)
                  ·
                    refine ⟨116123650014325264984957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2477304533638938986345749 116123650014325264984957)
                    ·
                      rfl

theorem cell23_678450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_678450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678450 prefixEnd_678450 := by exact prefixLift 678450
  have htrace : WordTrace (prefixWord ++ tailWord_678450) baseStart_678450 baseEnd_678450 := by
    simpa [prefixWord, tailWord_678450, baseEnd_678450] using wordTrace_append hprefix tailTrace_678450
  have hstable : (prefixWord ++ tailWord_678450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678450).length < 2 ^ (prefixWord ++ tailWord_678450).sum := by decide
  have hdescent : baseEnd_678450 < baseStart_678450 := by decide
  rcases family_descends (prefixWord ++ tailWord_678450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678461 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_678461 : Nat := 118140960795 + 678461 * 2 ^ 59
def prefixEnd_678461 : Nat := 4983230072969 + 3 ^ 40 * 678461 * 2
def baseEnd_678461 : Nat := 348376598330175251917321

theorem tailTrace_678461 : CollatzResearch.WordTrace tailWord_678461 prefixEnd_678461 348376598330175251917321 := by
  unfold tailWord_678461
  simp only [CollatzResearch.WordTrace]
  refine ⟨24745505595059143758875237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16497003730039429172583491 24745505595059143758875237)
  ·
    refine ⟨4639782299073589454789107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24745505595059143758875237 4639782299073589454789107)
    ·
      refine ⟨6959673448610384182183661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639782299073589454789107 6959673448610384182183661)
      ·
        refine ⟨2609877543228894068318873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6959673448610384182183661 2609877543228894068318873)
        ·
          refine ⟨1957408157421670551239155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2609877543228894068318873 1957408157421670551239155)
          ·
            refine ⟨2936112236132505826858733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957408157421670551239155 2936112236132505826858733)
            ·
              refine ⟨1101042088549689685072025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936112236132505826858733 1101042088549689685072025)
              ·
                refine ⟨825781566412267263804019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101042088549689685072025 825781566412267263804019)
                ·
                  refine ⟨1238672349618400895706029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 825781566412267263804019 1238672349618400895706029)
                  ·
                    refine ⟨464502131106900335889761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238672349618400895706029 464502131106900335889761)
                    ·
                      refine ⟨348376598330175251917321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464502131106900335889761 348376598330175251917321)
                      ·
                        rfl

theorem cell23_678461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_678461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678461 prefixEnd_678461 := by exact prefixLift 678461
  have htrace : WordTrace (prefixWord ++ tailWord_678461) baseStart_678461 baseEnd_678461 := by
    simpa [prefixWord, tailWord_678461, baseEnd_678461] using wordTrace_append hprefix tailTrace_678461
  have hstable : (prefixWord ++ tailWord_678461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678461).length < 2 ^ (prefixWord ++ tailWord_678461).sum := by decide
  have hdescent : baseEnd_678461 < baseStart_678461 := by decide
  rcases family_descends (prefixWord ++ tailWord_678461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678468 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_678468 : Nat := 118140960795 + 678468 * 2 ^ 59
def prefixEnd_678468 : Nat := 4983230072969 + 3 ^ 40 * 678468 * 2
def baseEnd_678468 : Nat := 348380192694756724529789

theorem tailTrace_678468 : CollatzResearch.WordTrace tailWord_678468 prefixEnd_678468 348380192694756724529789 := by
  unfold tailWord_678468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372880453016891977190029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16497173937355855969586705 12372880453016891977190029)
  ·
    refine ⟨4639830169881334491446261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12372880453016891977190029 4639830169881334491446261)
    ·
      refine ⟨434984078426375108573087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4639830169881334491446261 434984078426375108573087)
      ·
        refine ⟨652476117639562662859631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434984078426375108573087 652476117639562662859631)
        ·
          refine ⟨978714176459343994289447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652476117639562662859631 978714176459343994289447)
          ·
            refine ⟨1468071264689015991434171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978714176459343994289447 1468071264689015991434171)
            ·
              refine ⟨2202106897033523987151257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468071264689015991434171 2202106897033523987151257)
              ·
                refine ⟨1651580172775142990363443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202106897033523987151257 1651580172775142990363443)
                ·
                  refine ⟨2477370259162714485545165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651580172775142990363443 2477370259162714485545165)
                  ·
                    refine ⟨929013847186017932079437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477370259162714485545165 929013847186017932079437)
                    ·
                      refine ⟨348380192694756724529789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 929013847186017932079437 348380192694756724529789)
                      ·
                        rfl

theorem cell23_678468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_678468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678468 prefixEnd_678468 := by exact prefixLift 678468
  have htrace : WordTrace (prefixWord ++ tailWord_678468) baseStart_678468 baseEnd_678468 := by
    simpa [prefixWord, tailWord_678468, baseEnd_678468] using wordTrace_append hprefix tailTrace_678468
  have hstable : (prefixWord ++ tailWord_678468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678468).length < 2 ^ (prefixWord ++ tailWord_678468).sum := by decide
  have hdescent : baseEnd_678468 < baseStart_678468 := by decide
  rcases family_descends (prefixWord ++ tailWord_678468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678474 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_678474 : Nat := 118140960795 + 678474 * 2 ^ 59
def prefixEnd_678474 : Nat := 4983230072969 + 3 ^ 40 * 678474 * 2
def baseEnd_678474 : Nat := 348383273578683701054761

theorem tailTrace_678474 : CollatzResearch.WordTrace tailWord_678474 prefixEnd_678474 348383273578683701054761 := by
  unfold tailWord_678474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186494936003011744774619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16497319829341364652732317 6186494936003011744774619)
  ·
    refine ⟨9279742404004517617161929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6186494936003011744774619 9279742404004517617161929)
    ·
      refine ⟨6959806803003388212871447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9279742404004517617161929 6959806803003388212871447)
      ·
        refine ⟨10439710204505082319307171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959806803003388212871447 10439710204505082319307171)
        ·
          refine ⟨15659565306757623478960757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10439710204505082319307171 15659565306757623478960757)
          ·
            refine ⟨1468084247508527201152571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15659565306757623478960757 1468084247508527201152571)
            ·
              refine ⟨2202126371262790801728857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468084247508527201152571 2202126371262790801728857)
              ·
                refine ⟨1651594778447093101296643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202126371262790801728857 1651594778447093101296643)
                ·
                  refine ⟨2477392167670639651944965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651594778447093101296643 2477392167670639651944965)
                  ·
                    refine ⟨464511031438244934739681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477392167670639651944965 464511031438244934739681)
                    ·
                      refine ⟨348383273578683701054761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464511031438244934739681 348383273578683701054761)
                      ·
                        rfl

theorem cell23_678474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_678474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678474 prefixEnd_678474 := by exact prefixLift 678474
  have htrace : WordTrace (prefixWord ++ tailWord_678474) baseStart_678474 baseEnd_678474 := by
    simpa [prefixWord, tailWord_678474, baseEnd_678474] using wordTrace_append hprefix tailTrace_678474
  have hstable : (prefixWord ++ tailWord_678474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678474).length < 2 ^ (prefixWord ++ tailWord_678474).sum := by decide
  have hdescent : baseEnd_678474 < baseStart_678474 := by decide
  rcases family_descends (prefixWord ++ tailWord_678474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678504 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_678504 : Nat := 118140960795 + 678504 * 2 ^ 59
def prefixEnd_678504 : Nat := 4983230072969 + 3 ^ 40 * 678504 * 2
def baseEnd_678504 : Nat := 348398677998318583679623

theorem tailTrace_678504 : CollatzResearch.WordTrace tailWord_678504 prefixEnd_678504 348398677998318583679623 := by
  unfold tailWord_678504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373536966951681051345283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16498049289268908068460377 12373536966951681051345283)
  ·
    refine ⟨18560305450427521577017925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12373536966951681051345283 18560305450427521577017925)
    ·
      refine ⟨3480057271955160295690861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18560305450427521577017925 3480057271955160295690861)
      ·
        refine ⟨1305021476983185110884073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3480057271955160295690861 1305021476983185110884073)
        ·
          refine ⟨978766107737388833163055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1305021476983185110884073 978766107737388833163055)
          ·
            refine ⟨1468149161606083249744583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978766107737388833163055 1468149161606083249744583)
            ·
              refine ⟨2202223742409124874616875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468149161606083249744583 2202223742409124874616875)
              ·
                refine ⟨3303335613613687311925313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202223742409124874616875 3303335613613687311925313)
                ·
                  refine ⟨2477501710210265483943985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303335613613687311925313 2477501710210265483943985)
                  ·
                    refine ⟨1858126282657699112957989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2477501710210265483943985 1858126282657699112957989)
                    ·
                      refine ⟨348398677998318583679623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1858126282657699112957989 348398677998318583679623)
                      ·
                        rfl

theorem cell23_678504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_678504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678504 prefixEnd_678504 := by exact prefixLift 678504
  have htrace : WordTrace (prefixWord ++ tailWord_678504) baseStart_678504 baseEnd_678504 := by
    simpa [prefixWord, tailWord_678504, baseEnd_678504] using wordTrace_append hprefix tailTrace_678504
  have hstable : (prefixWord ++ tailWord_678504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678504).length < 2 ^ (prefixWord ++ tailWord_678504).sum := by decide
  have hdescent : baseEnd_678504 < baseStart_678504 := by decide
  rcases family_descends (prefixWord ++ tailWord_678504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678547 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 3, 6, 2]
def baseStart_678547 : Nat := 118140960795 + 678547 * 2 ^ 59
def prefixEnd_678547 : Nat := 4983230072969 + 3 ^ 40 * 678547 * 2
def baseEnd_678547 : Nat := 348420757666461915441925

theorem tailTrace_678547 : CollatzResearch.WordTrace tailWord_678547 prefixEnd_678547 348420757666461915441925 := by
  unfold tailWord_678547
  simp only [CollatzResearch.WordTrace]
  refine ⟨24748642272747580446505895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16499094848498386964337263 24748642272747580446505895)
  ·
    refine ⟨37122963409121370669758843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24748642272747580446505895 37122963409121370669758843)
    ·
      refine ⟨55684445113682056004638265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37122963409121370669758843 55684445113682056004638265)
      ·
        refine ⟨41763333835261542003478699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55684445113682056004638265 41763333835261542003478699)
        ·
          refine ⟨62645000752892313005218049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41763333835261542003478699 62645000752892313005218049)
          ·
            refine ⟨46983750564669234753913537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62645000752892313005218049 46983750564669234753913537)
            ·
              refine ⟨35237812923501926065435153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46983750564669234753913537 35237812923501926065435153)
              ·
                refine ⟨26428359692626444549076365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35237812923501926065435153 26428359692626444549076365)
                ·
                  refine ⟨9910634884734916705903637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26428359692626444549076365 9910634884734916705903637)
                  ·
                    refine ⟨464561010221949220589233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9910634884734916705903637 464561010221949220589233)
                    ·
                      refine ⟨348420757666461915441925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464561010221949220589233 348420757666461915441925)
                      ·
                        rfl

theorem cell23_678547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 6, 2].length) (baseStart_678547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678547 prefixEnd_678547 := by exact prefixLift 678547
  have htrace : WordTrace (prefixWord ++ tailWord_678547) baseStart_678547 baseEnd_678547 := by
    simpa [prefixWord, tailWord_678547, baseEnd_678547] using wordTrace_append hprefix tailTrace_678547
  have hstable : (prefixWord ++ tailWord_678547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678547).length < 2 ^ (prefixWord ++ tailWord_678547).sum := by decide
  have hdescent : baseEnd_678547 < baseStart_678547 := by decide
  rcases family_descends (prefixWord ++ tailWord_678547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678564 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_678564 : Nat := 118140960795 + 678564 * 2 ^ 59
def prefixEnd_678564 : Nat := 4983230072969 + 3 ^ 40 * 678564 * 2
def baseEnd_678564 : Nat := 348429486837588348929347

theorem tailTrace_678564 : CollatzResearch.WordTrace tailWord_678564 prefixEnd_678564 348429486837588348929347 := by
  unfold tailWord_678564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374631156842996174937373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16499508209123994899916497 12374631156842996174937373)
  ·
    refine ⟨4640486683816123565601515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12374631156842996174937373 4640486683816123565601515)
    ·
      refine ⟨6960730025724185348402273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640486683816123565601515 6960730025724185348402273)
      ·
        refine ⟨5220547519293139011301705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6960730025724185348402273 5220547519293139011301705)
        ·
          refine ⟨3915410639469854258476279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5220547519293139011301705 3915410639469854258476279)
          ·
            refine ⟨5873115959204781387714419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915410639469854258476279 5873115959204781387714419)
            ·
              refine ⟨8809673938807172081571629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873115959204781387714419 8809673938807172081571629)
              ·
                refine ⟨3303627727052689530589361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8809673938807172081571629 3303627727052689530589361)
                ·
                  refine ⟨2477720795289517147942021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303627727052689530589361 2477720795289517147942021)
                  ·
                    refine ⟨464572649116784465239129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477720795289517147942021 464572649116784465239129)
                    ·
                      refine ⟨348429486837588348929347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464572649116784465239129 348429486837588348929347)
                      ·
                        rfl

theorem cell23_678564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_678564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678564 prefixEnd_678564 := by exact prefixLift 678564
  have htrace : WordTrace (prefixWord ++ tailWord_678564) baseStart_678564 baseEnd_678564 := by
    simpa [prefixWord, tailWord_678564, baseEnd_678564] using wordTrace_append hprefix tailTrace_678564
  have hstable : (prefixWord ++ tailWord_678564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678564).length < 2 ^ (prefixWord ++ tailWord_678564).sum := by decide
  have hdescent : baseEnd_678564 < baseStart_678564 := by decide
  rcases family_descends (prefixWord ++ tailWord_678564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678591 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 1, 4]
def baseStart_678591 : Nat := 118140960795 + 678591 * 2 ^ 59
def prefixEnd_678591 : Nat := 4983230072969 + 3 ^ 40 * 678591 * 2
def baseEnd_678591 : Nat := 116147783605086581097241

theorem tailTrace_678591 : CollatzResearch.WordTrace tailWord_678591 prefixEnd_678591 116147783605086581097241 := by
  unfold tailWord_678591
  simp only [CollatzResearch.WordTrace]
  refine ⟨24750247084588175961107627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16500164723058783974071751 24750247084588175961107627)
  ·
    refine ⟨37125370626882263941661441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24750247084588175961107627 37125370626882263941661441)
    ·
      refine ⟨27844027970161697956246081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37125370626882263941661441 27844027970161697956246081)
      ·
        refine ⟨20883020977621273467184561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27844027970161697956246081 20883020977621273467184561)
        ·
          refine ⟨15662265733215955100388421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20883020977621273467184561 15662265733215955100388421)
          ·
            refine ⟨2936674824977991581322829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15662265733215955100388421 2936674824977991581322829)
            ·
              refine ⟨1101253059366746842996061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936674824977991581322829 1101253059366746842996061)
              ·
                refine ⟨412969897262530066123523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101253059366746842996061 412969897262530066123523)
                ·
                  refine ⟨619454845893795099185285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412969897262530066123523 619454845893795099185285)
                  ·
                    refine ⟨116147783605086581097241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 619454845893795099185285 116147783605086581097241)
                    ·
                      rfl

theorem cell23_678591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_678591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678591 prefixEnd_678591 := by exact prefixLift 678591
  have htrace : WordTrace (prefixWord ++ tailWord_678591) baseStart_678591 baseEnd_678591 := by
    simpa [prefixWord, tailWord_678591, baseEnd_678591] using wordTrace_append hprefix tailTrace_678591
  have hstable : (prefixWord ++ tailWord_678591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678591).length < 2 ^ (prefixWord ++ tailWord_678591).sum := by decide
  have hdescent : baseEnd_678591 < baseStart_678591 := by decide
  rcases family_descends (prefixWord ++ tailWord_678591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678617 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_678617 : Nat := 118140960795 + 678617 * 2 ^ 59
def prefixEnd_678617 : Nat := 4983230072969 + 3 ^ 40 * 678617 * 2
def baseEnd_678617 : Nat := 116152233770758880522201

theorem tailTrace_678617 : CollatzResearch.WordTrace tailWord_678617 prefixEnd_678617 116152233770758880522201 := by
  unfold tailWord_678617
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751195382493982401554105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16500796921662654934369403 24751195382493982401554105)
  ·
    refine ⟨18563396536870486801165579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24751195382493982401554105 18563396536870486801165579)
    ·
      refine ⟨27845094805305730201748369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18563396536870486801165579 27845094805305730201748369)
      ·
        refine ⟨20883821103979297651311277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27845094805305730201748369 20883821103979297651311277)
        ·
          refine ⟨7831432913992236619241729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20883821103979297651311277 7831432913992236619241729)
          ·
            refine ⟨5873574685494177464431297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831432913992236619241729 5873574685494177464431297)
            ·
              refine ⟨4405181014120633098323473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873574685494177464431297 4405181014120633098323473)
              ·
                refine ⟨3303885760590474823742605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4405181014120633098323473 3303885760590474823742605)
                ·
                  refine ⟨1238957160221428058903477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3303885760590474823742605 1238957160221428058903477)
                  ·
                    refine ⟨116152233770758880522201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1238957160221428058903477 116152233770758880522201)
                    ·
                      rfl

theorem cell23_678617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_678617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678617 prefixEnd_678617 := by exact prefixLift 678617
  have htrace : WordTrace (prefixWord ++ tailWord_678617) baseStart_678617 baseEnd_678617 := by
    simpa [prefixWord, tailWord_678617, baseEnd_678617] using wordTrace_append hprefix tailTrace_678617
  have hstable : (prefixWord ++ tailWord_678617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678617).length < 2 ^ (prefixWord ++ tailWord_678617).sum := by decide
  have hdescent : baseEnd_678617 < baseStart_678617 := by decide
  rcases family_descends (prefixWord ++ tailWord_678617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678624 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2]
def baseStart_678624 : Nat := 118140960795 + 678624 * 2 ^ 59
def prefixEnd_678624 : Nat := 4983230072969 + 3 ^ 40 * 678624 * 2
def baseEnd_678624 : Nat := 348460295676858114179071

theorem tailTrace_678624 : CollatzResearch.WordTrace tailWord_678624 prefixEnd_678624 348460295676858114179071 := by
  unfold tailWord_678624
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375725346734311298529463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16500967128979081731372617 12375725346734311298529463)
  ·
    refine ⟨18563588020101466947794195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12375725346734311298529463 18563588020101466947794195)
    ·
      refine ⟨27845382030152200421691293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18563588020101466947794195 27845382030152200421691293)
      ·
        refine ⟨10442018261307075158134235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27845382030152200421691293 10442018261307075158134235)
        ·
          refine ⟨15663027391960612737201353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442018261307075158134235 15663027391960612737201353)
          ·
            refine ⟨11747270543970459552901015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15663027391960612737201353 11747270543970459552901015)
            ·
              refine ⟨17620905815955689329351523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747270543970459552901015 17620905815955689329351523)
              ·
                refine ⟨26431358723933533994027285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17620905815955689329351523 26431358723933533994027285)
                ·
                  refine ⟨1238969940184384405970029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26431358723933533994027285 1238969940184384405970029)
                  ·
                    refine ⟨464613727569144152238761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1238969940184384405970029 464613727569144152238761)
                    ·
                      refine ⟨348460295676858114179071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464613727569144152238761 348460295676858114179071)
                      ·
                        rfl

theorem cell23_678624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_678624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678624 prefixEnd_678624 := by exact prefixLift 678624
  have htrace : WordTrace (prefixWord ++ tailWord_678624) baseStart_678624 baseEnd_678624 := by
    simpa [prefixWord, tailWord_678624, baseEnd_678624] using wordTrace_append hprefix tailTrace_678624
  have hstable : (prefixWord ++ tailWord_678624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678624).length < 2 ^ (prefixWord ++ tailWord_678624).sum := by decide
  have hdescent : baseEnd_678624 < baseStart_678624 := by decide
  rcases family_descends (prefixWord ++ tailWord_678624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678641 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_678641 : Nat := 118140960795 + 678641 * 2 ^ 59
def prefixEnd_678641 : Nat := 4983230072969 + 3 ^ 40 * 678641 * 2
def baseEnd_678641 : Nat := 348469024847984547666493

theorem tailTrace_678641 : CollatzResearch.WordTrace tailWord_678641 prefixEnd_678641 348469024847984547666493 := by
  unfold tailWord_678641
  simp only [CollatzResearch.WordTrace]
  refine ⟨24752070734407034500427777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16501380489604689666951851 24752070734407034500427777)
  ·
    refine ⟨18564053050805275875320833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24752070734407034500427777 18564053050805275875320833)
    ·
      refine ⟨13923039788103956906490625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18564053050805275875320833 13923039788103956906490625)
      ·
        refine ⟨10442279841077967679867969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13923039788103956906490625 10442279841077967679867969)
        ·
          refine ⟨7831709880808475759900977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10442279841077967679867969 7831709880808475759900977)
          ·
            refine ⟨5873782410606356819925733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831709880808475759900977 5873782410606356819925733)
            ·
              refine ⟨1101334201988691903736075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5873782410606356819925733 1101334201988691903736075)
              ·
                refine ⟨1652001302983037855604113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101334201988691903736075 1652001302983037855604113)
                ·
                  refine ⟨1239000977237278391703085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652001302983037855604113 1239000977237278391703085)
                  ·
                    refine ⟨464625366463979396888657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239000977237278391703085 464625366463979396888657)
                    ·
                      refine ⟨348469024847984547666493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464625366463979396888657 348469024847984547666493)
                      ·
                        rfl

theorem cell23_678641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_678641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678641 prefixEnd_678641 := by exact prefixLift 678641
  have htrace : WordTrace (prefixWord ++ tailWord_678641) baseStart_678641 baseEnd_678641 := by
    simpa [prefixWord, tailWord_678641, baseEnd_678641] using wordTrace_append hprefix tailTrace_678641
  have hstable : (prefixWord ++ tailWord_678641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678641).length < 2 ^ (prefixWord ++ tailWord_678641).sum := by decide
  have hdescent : baseEnd_678641 < baseStart_678641 := by decide
  rcases family_descends (prefixWord ++ tailWord_678641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678658 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_678658 : Nat := 118140960795 + 678658 * 2 ^ 59
def prefixEnd_678658 : Nat := 4983230072969 + 3 ^ 40 * 678658 * 2
def baseEnd_678658 : Nat := 348477754019110981153915

theorem tailTrace_678658 : CollatzResearch.WordTrace tailWord_678658 prefixEnd_678658 348477754019110981153915 := by
  unfold tailWord_678658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188172693836361600949157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16501793850230297602531085 6188172693836361600949157)
  ·
    refine ⟨1160282380094317800177967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6188172693836361600949157 1160282380094317800177967)
    ·
      refine ⟨1740423570141476700266951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1160282380094317800177967 1740423570141476700266951)
      ·
        refine ⟨2610635355212215050400427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740423570141476700266951 2610635355212215050400427)
        ·
          refine ⟨3915953032818322575600641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610635355212215050400427 3915953032818322575600641)
          ·
            refine ⟨2936964774613741931700481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915953032818322575600641 2936964774613741931700481)
            ·
              refine ⟨2202723580960306448775361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936964774613741931700481 2202723580960306448775361)
              ·
                refine ⟨1652042685720229836581521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202723580960306448775361 1652042685720229836581521)
                ·
                  refine ⟨1239032014290172377436141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652042685720229836581521 1239032014290172377436141)
                  ·
                    refine ⟨464637005358814641538553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239032014290172377436141 464637005358814641538553)
                    ·
                      refine ⟨348477754019110981153915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464637005358814641538553 348477754019110981153915)
                      ·
                        rfl

theorem cell23_678658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_678658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678658 prefixEnd_678658 := by exact prefixLift 678658
  have htrace : WordTrace (prefixWord ++ tailWord_678658) baseStart_678658 baseEnd_678658 := by
    simpa [prefixWord, tailWord_678658, baseEnd_678658] using wordTrace_append hprefix tailTrace_678658
  have hstable : (prefixWord ++ tailWord_678658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678658).length < 2 ^ (prefixWord ++ tailWord_678658).sum := by decide
  have hdescent : baseEnd_678658 < baseStart_678658 := by decide
  rcases family_descends (prefixWord ++ tailWord_678658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678667 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_678667 : Nat := 118140960795 + 678667 * 2 ^ 59
def prefixEnd_678667 : Nat := 4983230072969 + 3 ^ 40 * 678667 * 2
def baseEnd_678667 : Nat := 348482375345001445941373

theorem tailTrace_678667 : CollatzResearch.WordTrace tailWord_678667 prefixEnd_678667 348482375345001445941373 := by
  unfold tailWord_678667
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753019032312840940874255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502012688208560627249503 24753019032312840940874255)
  ·
    refine ⟨37129528548469261411311383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24753019032312840940874255 37129528548469261411311383)
    ·
      refine ⟨55694292822703892116967075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37129528548469261411311383 55694292822703892116967075)
      ·
        refine ⟨83541439234055838175450613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55694292822703892116967075 83541439234055838175450613)
        ·
          refine ⟨7832009928192734828948495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83541439234055838175450613 7832009928192734828948495)
          ·
            refine ⟨11748014892289102243422743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832009928192734828948495 11748014892289102243422743)
            ·
              refine ⟨17622022338433653365134115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748014892289102243422743 17622022338433653365134115)
              ·
                refine ⟨26433033507650480047701173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17622022338433653365134115 26433033507650480047701173)
                ·
                  refine ⟨2478096891342232504471985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26433033507650480047701173 2478096891342232504471985)
                  ·
                    refine ⟨1858572668506674378353989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478096891342232504471985 1858572668506674378353989)
                    ·
                      refine ⟨348482375345001445941373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1858572668506674378353989 348482375345001445941373)
                      ·
                        rfl

theorem cell23_678667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_678667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678667 prefixEnd_678667 := by exact prefixLift 678667
  have htrace : WordTrace (prefixWord ++ tailWord_678667) baseStart_678667 baseEnd_678667 := by
    simpa [prefixWord, tailWord_678667, baseEnd_678667] using wordTrace_append hprefix tailTrace_678667
  have hstable : (prefixWord ++ tailWord_678667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678667).length < 2 ^ (prefixWord ++ tailWord_678667).sum := by decide
  have hdescent : baseEnd_678667 < baseStart_678667 := by decide
  rcases family_descends (prefixWord ++ tailWord_678667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678671 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 3, 2, 2]
def baseStart_678671 : Nat := 118140960795 + 678671 * 2 ^ 59
def prefixEnd_678671 : Nat := 4983230072969 + 3 ^ 40 * 678671 * 2
def baseEnd_678671 : Nat := 348484429267619430291355

theorem tailTrace_678671 : CollatzResearch.WordTrace tailWord_678671 prefixEnd_678671 348484429267619430291355 := by
  unfold tailWord_678671
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753164924298349624019867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502109949532233082679911 24753164924298349624019867)
  ·
    refine ⟨37129747386447524436029801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24753164924298349624019867 37129747386447524436029801)
    ·
      refine ⟨27847310539835643327022351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37129747386447524436029801 27847310539835643327022351)
      ·
        refine ⟨41770965809753464990533527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847310539835643327022351 41770965809753464990533527)
        ·
          refine ⟨62656448714630197485800291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41770965809753464990533527 62656448714630197485800291)
          ·
            refine ⟨93984673071945296228700437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62656448714630197485800291 93984673071945296228700437)
            ·
              refine ⟨4405531550247435760720333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93984673071945296228700437 4405531550247435760720333)
              ·
                refine ⟨1652074331342788410270125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405531550247435760720333 1652074331342788410270125)
                ·
                  refine ⟨619527874253545653851297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1652074331342788410270125 619527874253545653851297)
                  ·
                    refine ⟨464645905690159240388473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619527874253545653851297 464645905690159240388473)
                    ·
                      refine ⟨348484429267619430291355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464645905690159240388473 348484429267619430291355)
                      ·
                        rfl

theorem cell23_678671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 2, 2].length) (baseStart_678671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678671 prefixEnd_678671 := by exact prefixLift 678671
  have htrace : WordTrace (prefixWord ++ tailWord_678671) baseStart_678671 baseEnd_678671 := by
    simpa [prefixWord, tailWord_678671, baseEnd_678671] using wordTrace_append hprefix tailTrace_678671
  have hstable : (prefixWord ++ tailWord_678671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678671).length < 2 ^ (prefixWord ++ tailWord_678671).sum := by decide
  have hdescent : baseEnd_678671 < baseStart_678671 := by decide
  rcases family_descends (prefixWord ++ tailWord_678671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678684 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_678684 : Nat := 118140960795 + 678684 * 2 ^ 59
def prefixEnd_678684 : Nat := 4983230072969 + 3 ^ 40 * 678684 * 2
def baseEnd_678684 : Nat := 348491104516127879428795

theorem tailTrace_678684 : CollatzResearch.WordTrace tailWord_678684 prefixEnd_678684 348491104516127879428795 := by
  unfold tailWord_678684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376819536625626422121553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16502426048834168562828737 12376819536625626422121553)
  ·
    refine ⟨9282614652469219816591165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12376819536625626422121553 9282614652469219816591165)
    ·
      refine ⟨3480980494675957431221687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9282614652469219816591165 3480980494675957431221687)
      ·
        refine ⟨5221470742013936146832531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480980494675957431221687 5221470742013936146832531)
        ·
          refine ⟨7832206113020904220248797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221470742013936146832531 7832206113020904220248797)
          ·
            refine ⟨2937077292382839082593299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7832206113020904220248797 2937077292382839082593299)
            ·
              refine ⟨4405615938574258623889949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937077292382839082593299 4405615938574258623889949)
              ·
                refine ⟨1652105976965346983958731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405615938574258623889949 1652105976965346983958731)
                ·
                  refine ⟨2478158965448020475938097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652105976965346983958731 2478158965448020475938097)
                  ·
                    refine ⟨1858619224086015356953573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2478158965448020475938097 1858619224086015356953573)
                    ·
                      refine ⟨348491104516127879428795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1858619224086015356953573 348491104516127879428795)
                      ·
                        rfl

theorem cell23_678684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_678684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678684 prefixEnd_678684 := by exact prefixLift 678684
  have htrace : WordTrace (prefixWord ++ tailWord_678684) baseStart_678684 baseEnd_678684 := by
    simpa [prefixWord, tailWord_678684, baseEnd_678684] using wordTrace_append hprefix tailTrace_678684
  have hstable : (prefixWord ++ tailWord_678684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678684).length < 2 ^ (prefixWord ++ tailWord_678684).sum := by decide
  have hdescent : baseEnd_678684 < baseStart_678684 := by decide
  rcases family_descends (prefixWord ++ tailWord_678684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678688 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2]
def baseStart_678688 : Nat := 118140960795 + 678688 * 2 ^ 59
def prefixEnd_678688 : Nat := 4983230072969 + 3 ^ 40 * 678688 * 2
def baseEnd_678688 : Nat := 348493158438745863778777

theorem tailTrace_678688 : CollatzResearch.WordTrace tailWord_678688 prefixEnd_678688 348493158438745863778777 := by
  unfold tailWord_678688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376892482618380763694359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16502523310157841018259145 12376892482618380763694359)
  ·
    refine ⟨18565338723927571145541539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376892482618380763694359 18565338723927571145541539)
    ·
      refine ⟨27848008085891356718312309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18565338723927571145541539 27848008085891356718312309)
      ·
        refine ⟨2610750758052314692341779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27848008085891356718312309 2610750758052314692341779)
        ·
          refine ⟨3916126137078472038512669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610750758052314692341779 3916126137078472038512669)
          ·
            refine ⟨1468547301404427014442251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3916126137078472038512669 1468547301404427014442251)
            ·
              refine ⟨2202820952106640521663377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468547301404427014442251 2202820952106640521663377)
              ·
                refine ⟨1652115714079980391247533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202820952106640521663377 1652115714079980391247533)
                ·
                  refine ⟨619543392779992646717825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1652115714079980391247533 619543392779992646717825)
                  ·
                    refine ⟨464657544584994485038369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619543392779992646717825 464657544584994485038369)
                    ·
                      refine ⟨348493158438745863778777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464657544584994485038369 348493158438745863778777)
                      ·
                        rfl

theorem cell23_678688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_678688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678688 prefixEnd_678688 := by exact prefixLift 678688
  have htrace : WordTrace (prefixWord ++ tailWord_678688) baseStart_678688 baseEnd_678688 := by
    simpa [prefixWord, tailWord_678688, baseEnd_678688] using wordTrace_append hprefix tailTrace_678688
  have hstable : (prefixWord ++ tailWord_678688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678688).length < 2 ^ (prefixWord ++ tailWord_678688).sum := by decide
  have hdescent : baseEnd_678688 < baseStart_678688 := by decide
  rcases family_descends (prefixWord ++ tailWord_678688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678705 : List Nat := [1, 2, 2, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_678705 : Nat := 118140960795 + 678705 * 2 ^ 59
def prefixEnd_678705 : Nat := 4983230072969 + 3 ^ 40 * 678705 * 2
def baseEnd_678705 : Nat := 348501887609872297266199

theorem tailTrace_678705 : CollatzResearch.WordTrace tailWord_678705 prefixEnd_678705 348501887609872297266199 := by
  unfold tailWord_678705
  simp only [CollatzResearch.WordTrace]
  refine ⟨24754405006175173430757569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16502936670783448953838379 24754405006175173430757569)
  ·
    refine ⟨18565803754631380073068177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24754405006175173430757569 18565803754631380073068177)
    ·
      refine ⟨13924352815973535054801133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18565803754631380073068177 13924352815973535054801133)
      ·
        refine ⟨5221632305990075645550425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13924352815973535054801133 5221632305990075645550425)
        ·
          refine ⟨3916224229492556734162819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5221632305990075645550425 3916224229492556734162819)
          ·
            refine ⟨5874336344238835101244229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916224229492556734162819 5874336344238835101244229)
            ·
              refine ⟨1101438064544781581483293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5874336344238835101244229 1101438064544781581483293)
              ·
                refine ⟨413039274204293093056235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1101438064544781581483293 413039274204293093056235)
                ·
                  refine ⟨619558911306439639584353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413039274204293093056235 619558911306439639584353)
                  ·
                    refine ⟨464669183479829729688265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619558911306439639584353 464669183479829729688265)
                    ·
                      refine ⟨348501887609872297266199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464669183479829729688265 348501887609872297266199)
                      ·
                        rfl

theorem cell23_678705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_678705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678705 prefixEnd_678705 := by exact prefixLift 678705
  have htrace : WordTrace (prefixWord ++ tailWord_678705) baseStart_678705 baseEnd_678705 := by
    simpa [prefixWord, tailWord_678705, baseEnd_678705] using wordTrace_append hprefix tailTrace_678705
  have hstable : (prefixWord ++ tailWord_678705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678705).length < 2 ^ (prefixWord ++ tailWord_678705).sum := by decide
  have hdescent : baseEnd_678705 < baseStart_678705 := by decide
  rcases family_descends (prefixWord ++ tailWord_678705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678764 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_678764 : Nat := 118140960795 + 678764 * 2 ^ 59
def prefixEnd_678764 : Nat := 4983230072969 + 3 ^ 40 * 678764 * 2
def baseEnd_678764 : Nat := 348532182968487566428427

theorem tailTrace_678764 : CollatzResearch.WordTrace tailWord_678764 prefixEnd_678764 348532182968487566428427 := by
  unfold tailWord_678764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378278456480713253577673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16504371275307617671436897 12378278456480713253577673)
  ·
    refine ⟨9283708842360534940183255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12378278456480713253577673 9283708842360534940183255)
    ·
      refine ⟨13925563263540802410274883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9283708842360534940183255 13925563263540802410274883)
      ·
        refine ⟨20888344895311203615412325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925563263540802410274883 20888344895311203615412325)
        ·
          refine ⟨3916564667870850677889811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20888344895311203615412325 3916564667870850677889811)
          ·
            refine ⟨5874847001806276016834717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916564667870850677889811 5874847001806276016834717)
            ·
              refine ⟨2203067625677353506313019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5874847001806276016834717 2203067625677353506313019)
              ·
                refine ⟨3304601438516030259469529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203067625677353506313019 3304601438516030259469529)
                ·
                  refine ⟨2478451078887022694602147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3304601438516030259469529 2478451078887022694602147)
                  ·
                    refine ⟨3717676618330534041903221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2478451078887022694602147 3717676618330534041903221)
                    ·
                      refine ⟨348532182968487566428427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3717676618330534041903221 348532182968487566428427)
                      ·
                        rfl

theorem cell23_678764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_678764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678764 prefixEnd_678764 := by exact prefixLift 678764
  have htrace : WordTrace (prefixWord ++ tailWord_678764) baseStart_678764 baseEnd_678764 := by
    simpa [prefixWord, tailWord_678764, baseEnd_678764] using wordTrace_append hprefix tailTrace_678764
  have hstable : (prefixWord ++ tailWord_678764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678764).length < 2 ^ (prefixWord ++ tailWord_678764).sum := by decide
  have hdescent : baseEnd_678764 < baseStart_678764 := by decide
  rcases family_descends (prefixWord ++ tailWord_678764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678767 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 9]
def baseStart_678767 : Nat := 118140960795 + 678767 * 2 ^ 59
def prefixEnd_678767 : Nat := 4983230072969 + 3 ^ 40 * 678767 * 2
def baseEnd_678767 : Nat := 38725969267827894965657

theorem tailTrace_678767 : CollatzResearch.WordTrace tailWord_678767 prefixEnd_678767 38725969267827894965657 := by
  unfold tailWord_678767
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756666331950558019514555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16504444221300372013009703 24756666331950558019514555)
  ·
    refine ⟨37134999497925837029271833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24756666331950558019514555 37134999497925837029271833)
    ·
      refine ⟨27851249623444377771953875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37134999497925837029271833 27851249623444377771953875)
      ·
        refine ⟨41776874435166566657930813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27851249623444377771953875 41776874435166566657930813)
        ·
          refine ⟨15666327913187462496724055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41776874435166566657930813 15666327913187462496724055)
          ·
            refine ⟨23499491869781193745086083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15666327913187462496724055 23499491869781193745086083)
            ·
              refine ⟨35249237804671790617629125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23499491869781193745086083 35249237804671790617629125)
              ·
                refine ⟨6609232088375960740805461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35249237804671790617629125 6609232088375960740805461)
                ·
                  refine ⟨38725969267827894965657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6609232088375960740805461 38725969267827894965657)
                  ·
                    rfl

theorem cell23_678767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 9].length) (baseStart_678767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678767 prefixEnd_678767 := by exact prefixLift 678767
  have htrace : WordTrace (prefixWord ++ tailWord_678767) baseStart_678767 baseEnd_678767 := by
    simpa [prefixWord, tailWord_678767, baseEnd_678767] using wordTrace_append hprefix tailTrace_678767
  have hstable : (prefixWord ++ tailWord_678767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678767).length < 2 ^ (prefixWord ++ tailWord_678767).sum := by decide
  have hdescent : baseEnd_678767 < baseStart_678767 := by decide
  rcases family_descends (prefixWord ++ tailWord_678767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678778 : List Nat := [3, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_678778 : Nat := 118140960795 + 678778 * 2 ^ 59
def prefixEnd_678778 : Nat := 4983230072969 + 3 ^ 40 * 678778 * 2
def baseEnd_678778 : Nat := 348539371697650511653363

theorem tailTrace_678778 : CollatzResearch.WordTrace tailWord_678778 prefixEnd_678778 348539371697650511653363 := by
  unfold tailWord_678778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189266883727676724541247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16504711689940471265443325 6189266883727676724541247)
  ·
    refine ⟨9283900325591515086811871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6189266883727676724541247 9283900325591515086811871)
    ·
      refine ⟨13925850488387272630217807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9283900325591515086811871 13925850488387272630217807)
      ·
        refine ⟨20888775732580908945326711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925850488387272630217807 20888775732580908945326711)
        ·
          refine ⟨31333163598871363417990067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888775732580908945326711 31333163598871363417990067)
          ·
            refine ⟨46999745398307045126985101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31333163598871363417990067 46999745398307045126985101)
            ·
              refine ⟨17624904524365141922619413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46999745398307045126985101 17624904524365141922619413)
              ·
                refine ⟨826167399579616027622785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17624904524365141922619413 826167399579616027622785)
                ·
                  refine ⟨619625549684712020717089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826167399579616027622785 619625549684712020717089)
                  ·
                    refine ⟨464719162263534015537817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619625549684712020717089 464719162263534015537817)
                    ·
                      refine ⟨348539371697650511653363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464719162263534015537817 348539371697650511653363)
                      ·
                        rfl

theorem cell23_678778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_678778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678778 prefixEnd_678778 := by exact prefixLift 678778
  have htrace : WordTrace (prefixWord ++ tailWord_678778) baseStart_678778 baseEnd_678778 := by
    simpa [prefixWord, tailWord_678778, baseEnd_678778] using wordTrace_append hprefix tailTrace_678778
  have hstable : (prefixWord ++ tailWord_678778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678778).length < 2 ^ (prefixWord ++ tailWord_678778).sum := by decide
  have hdescent : baseEnd_678778 < baseStart_678778 := by decide
  rcases family_descends (prefixWord ++ tailWord_678778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678795 : List Nat := [1, 1, 1, 1, 4, 2, 6, 1, 2, 2, 2]
def baseStart_678795 : Nat := 118140960795 + 678795 * 2 ^ 59
def prefixEnd_678795 : Nat := 4983230072969 + 3 ^ 40 * 678795 * 2
def baseEnd_678795 : Nat := 348548100868776945140785

theorem tailTrace_678795 : CollatzResearch.WordTrace tailWord_678795 prefixEnd_678795 348548100868776945140785 := by
  unfold tailWord_678795
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757687575849118801533839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16505125050566079201022559 24757687575849118801533839)
  ·
    refine ⟨37136531363773678202300759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24757687575849118801533839 37136531363773678202300759)
    ·
      refine ⟨55704797045660517303451139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37136531363773678202300759 55704797045660517303451139)
      ·
        refine ⟨83557195568490775955176709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55704797045660517303451139 83557195568490775955176709)
        ·
          refine ⟨15666974169092020491595633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83557195568490775955176709 15666974169092020491595633)
          ·
            refine ⟨11750230626819015368696725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15666974169092020491595633 11750230626819015368696725)
            ·
              refine ⟨550792060632141345407659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11750230626819015368696725 550792060632141345407659)
              ·
                refine ⟨826188090948212018111489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550792060632141345407659 826188090948212018111489)
                ·
                  refine ⟨619641068211159013583617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826188090948212018111489 619641068211159013583617)
                  ·
                    refine ⟨464730801158369260187713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619641068211159013583617 464730801158369260187713)
                    ·
                      refine ⟨348548100868776945140785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464730801158369260187713 348548100868776945140785)
                      ·
                        rfl

theorem cell23_678795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 2, 2, 2].length) (baseStart_678795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678795 prefixEnd_678795 := by exact prefixLift 678795
  have htrace : WordTrace (prefixWord ++ tailWord_678795) baseStart_678795 baseEnd_678795 := by
    simpa [prefixWord, tailWord_678795, baseEnd_678795] using wordTrace_append hprefix tailTrace_678795
  have hstable : (prefixWord ++ tailWord_678795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678795).length < 2 ^ (prefixWord ++ tailWord_678795).sum := by decide
  have hdescent : baseEnd_678795 < baseStart_678795 := by decide
  rcases family_descends (prefixWord ++ tailWord_678795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678829 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_678829 : Nat := 118140960795 + 678829 * 2 ^ 59
def prefixEnd_678829 : Nat := 4983230072969 + 3 ^ 40 * 678829 * 2
def baseEnd_678829 : Nat := 348565559211029812115629

theorem tailTrace_678829 : CollatzResearch.WordTrace tailWord_678829 prefixEnd_678829 348565559211029812115629 := by
  unfold tailWord_678829
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758927657725942608271541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16505951771817295072181027 24758927657725942608271541)
  ·
    refine ⟨2321149467911807119525457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24758927657725942608271541 2321149467911807119525457)
    ·
      refine ⟨1740862100933855339644093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321149467911807119525457 1740862100933855339644093)
      ·
        refine ⟨652823287850195752366535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1740862100933855339644093 652823287850195752366535)
        ·
          refine ⟨979234931775293628549803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652823287850195752366535 979234931775293628549803)
          ·
            refine ⟨1468852397662940442824705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979234931775293628549803 1468852397662940442824705)
            ·
              refine ⟨1101639298247205332118529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1468852397662940442824705 1101639298247205332118529)
              ·
                refine ⟨826229473685403999088897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101639298247205332118529 826229473685403999088897)
                ·
                  refine ⟨619672105264052999316673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826229473685403999088897 619672105264052999316673)
                  ·
                    refine ⟨464754078948039749487505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619672105264052999316673 464754078948039749487505)
                    ·
                      refine ⟨348565559211029812115629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464754078948039749487505 348565559211029812115629)
                      ·
                        rfl

theorem cell23_678829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_678829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678829 prefixEnd_678829 := by exact prefixLift 678829
  have htrace : WordTrace (prefixWord ++ tailWord_678829) baseStart_678829 baseEnd_678829 := by
    simpa [prefixWord, tailWord_678829, baseEnd_678829] using wordTrace_append hprefix tailTrace_678829
  have hstable : (prefixWord ++ tailWord_678829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678829).length < 2 ^ (prefixWord ++ tailWord_678829).sum := by decide
  have hdescent : baseEnd_678829 < baseStart_678829 := by decide
  rcases family_descends (prefixWord ++ tailWord_678829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678834 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_678834 : Nat := 118140960795 + 678834 * 2 ^ 59
def prefixEnd_678834 : Nat := 4983230072969 + 3 ^ 40 * 678834 * 2
def baseEnd_678834 : Nat := 348568126614302292553105

theorem tailTrace_678834 : CollatzResearch.WordTrace tailWord_678834 prefixEnd_678834 348568126614302292553105 := by
  unfold tailWord_678834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189777505676957115550889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16506073348471885641469037 6189777505676957115550889)
  ·
    refine ⟨4642333129257717836663167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6189777505676957115550889 4642333129257717836663167)
    ·
      refine ⟨6963499693886576754994751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4642333129257717836663167 6963499693886576754994751)
      ·
        refine ⟨10445249540829865132492127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963499693886576754994751 10445249540829865132492127)
        ·
          refine ⟨15667874311244797698738191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10445249540829865132492127 15667874311244797698738191)
          ·
            refine ⟨23501811466867196548107287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15667874311244797698738191 23501811466867196548107287)
            ·
              refine ⟨35252717200300794822160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23501811466867196548107287 35252717200300794822160931)
              ·
                refine ⟨52879075800451192233241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35252717200300794822160931 52879075800451192233241397)
                ·
                  refine ⟨4957413356292299271866381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52879075800451192233241397 4957413356292299271866381)
                  ·
                    refine ⟨1859030008609612226949893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4957413356292299271866381 1859030008609612226949893)
                    ·
                      refine ⟨348568126614302292553105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1859030008609612226949893 348568126614302292553105)
                      ·
                        rfl

theorem cell23_678834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_678834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678834 prefixEnd_678834 := by exact prefixLift 678834
  have htrace : WordTrace (prefixWord ++ tailWord_678834) baseStart_678834 baseEnd_678834 := by
    simpa [prefixWord, tailWord_678834, baseEnd_678834] using wordTrace_append hprefix tailTrace_678834
  have hstable : (prefixWord ++ tailWord_678834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678834).length < 2 ^ (prefixWord ++ tailWord_678834).sum := by decide
  have hdescent : baseEnd_678834 < baseStart_678834 := by decide
  rcases family_descends (prefixWord ++ tailWord_678834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678851 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 2, 4, 2]
def baseStart_678851 : Nat := 118140960795 + 678851 * 2 ^ 59
def prefixEnd_678851 : Nat := 4983230072969 + 3 ^ 40 * 678851 * 2
def baseEnd_678851 : Nat := 348576855785428726040527

theorem tailTrace_678851 : CollatzResearch.WordTrace tailWord_678851 prefixEnd_678851 348576855785428726040527 := by
  unfold tailWord_678851
  simp only [CollatzResearch.WordTrace]
  refine ⟨24759730063646240365572407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16506486709097493577048271 24759730063646240365572407)
  ·
    refine ⟨37139595095469360548358611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24759730063646240365572407 37139595095469360548358611)
    ·
      refine ⟨55709392643204040822537917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37139595095469360548358611 55709392643204040822537917)
      ·
        refine ⟨20891022241201515308451719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55709392643204040822537917 20891022241201515308451719)
        ·
          refine ⟨31336533361802272962677579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20891022241201515308451719 31336533361802272962677579)
          ·
            refine ⟨47004800042703409444016369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31336533361802272962677579 47004800042703409444016369)
            ·
              refine ⟨35253600032027557083012277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47004800042703409444016369 35253600032027557083012277)
              ·
                refine ⟨3305025003002583476532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35253600032027557083012277 3305025003002583476532401)
                ·
                  refine ⟨2478768752251937607399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305025003002583476532401 2478768752251937607399301)
                  ·
                    refine ⟨464769141047238301387369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2478768752251937607399301 464769141047238301387369)
                    ·
                      refine ⟨348576855785428726040527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464769141047238301387369 348576855785428726040527)
                      ·
                        rfl

theorem cell23_678851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_678851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678851 prefixEnd_678851 := by exact prefixLift 678851
  have htrace : WordTrace (prefixWord ++ tailWord_678851) baseStart_678851 baseEnd_678851 := by
    simpa [prefixWord, tailWord_678851, baseEnd_678851] using wordTrace_append hprefix tailTrace_678851
  have hstable : (prefixWord ++ tailWord_678851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678851).length < 2 ^ (prefixWord ++ tailWord_678851).sum := by decide
  have hdescent : baseEnd_678851 < baseStart_678851 := by decide
  rcases family_descends (prefixWord ++ tailWord_678851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678868 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_678868 : Nat := 118140960795 + 678868 * 2 ^ 59
def prefixEnd_678868 : Nat := 4983230072969 + 3 ^ 40 * 678868 * 2
def baseEnd_678868 : Nat := 348585584956555159527949

theorem tailTrace_678868 : CollatzResearch.WordTrace tailWord_678868 prefixEnd_678868 348585584956555159527949 := by
  unfold tailWord_678868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380175052292326134470629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16506900069723101512627505 12380175052292326134470629)
  ·
    refine ⟨2321282822304811150213243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12380175052292326134470629 2321282822304811150213243)
    ·
      refine ⟨3481924233457216725319865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321282822304811150213243 3481924233457216725319865)
      ·
        refine ⟨2611443175092912543989899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3481924233457216725319865 2611443175092912543989899)
        ·
          refine ⟨3917164762639368815984849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611443175092912543989899 3917164762639368815984849)
          ·
            refine ⟨2937873571979526611988637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3917164762639368815984849 2937873571979526611988637)
            ·
              refine ⟨1101702589492322479495739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2937873571979526611988637 1101702589492322479495739)
              ·
                refine ⟨1652553884238483719243609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101702589492322479495739 1652553884238483719243609)
                ·
                  refine ⟨1239415413178862789432707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652553884238483719243609 1239415413178862789432707)
                  ·
                    refine ⟨1859123119768294184149061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239415413178862789432707 1859123119768294184149061)
                    ·
                      refine ⟨348585584956555159527949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1859123119768294184149061 348585584956555159527949)
                      ·
                        rfl

theorem cell23_678868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_678868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678868 prefixEnd_678868 := by exact prefixLift 678868
  have htrace : WordTrace (prefixWord ++ tailWord_678868) baseStart_678868 baseEnd_678868 := by
    simpa [prefixWord, tailWord_678868, baseEnd_678868] using wordTrace_append hprefix tailTrace_678868
  have hstable : (prefixWord ++ tailWord_678868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678868).length < 2 ^ (prefixWord ++ tailWord_678868).sum := by decide
  have hdescent : baseEnd_678868 < baseStart_678868 := by decide
  rcases family_descends (prefixWord ++ tailWord_678868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678871 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_678871 : Nat := 118140960795 + 678871 * 2 ^ 59
def prefixEnd_678871 : Nat := 4983230072969 + 3 ^ 40 * 678871 * 2
def baseEnd_678871 : Nat := 348587125398518647790435

theorem tailTrace_678871 : CollatzResearch.WordTrace tailWord_678871 prefixEnd_678871 348587125398518647790435 := by
  unfold tailWord_678871
  simp only [CollatzResearch.WordTrace]
  refine ⟨24760459523573783781300467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16506973015715855854200311 24760459523573783781300467)
  ·
    refine ⟨37140689285360675671950701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24760459523573783781300467 37140689285360675671950701)
    ·
      refine ⟨13927758482010253376981513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37140689285360675671950701 13927758482010253376981513)
      ·
        refine ⟨10445818861507690032736135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13927758482010253376981513 10445818861507690032736135)
        ·
          refine ⟨15668728292261535049104203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10445818861507690032736135 15668728292261535049104203)
          ·
            refine ⟨23503092438392302573656305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15668728292261535049104203 23503092438392302573656305)
            ·
              refine ⟨17627319328794226930242229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23503092438392302573656305 17627319328794226930242229)
              ·
                refine ⟨1652561187074458774710209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17627319328794226930242229 1652561187074458774710209)
                ·
                  refine ⟨1239420890305844081032657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652561187074458774710209 1239420890305844081032657)
                  ·
                    refine ⟨929565667729383060774493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1239420890305844081032657 929565667729383060774493)
                    ·
                      refine ⟨348587125398518647790435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 929565667729383060774493 348587125398518647790435)
                      ·
                        rfl

theorem cell23_678871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_678871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678871 prefixEnd_678871 := by exact prefixLift 678871
  have htrace : WordTrace (prefixWord ++ tailWord_678871) baseStart_678871 baseEnd_678871 := by
    simpa [prefixWord, tailWord_678871, baseEnd_678871] using wordTrace_append hprefix tailTrace_678871
  have hstable : (prefixWord ++ tailWord_678871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678871).length < 2 ^ (prefixWord ++ tailWord_678871).sum := by decide
  have hdescent : baseEnd_678871 < baseStart_678871 := by decide
  rcases family_descends (prefixWord ++ tailWord_678871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678908 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 6]
def baseStart_678908 : Nat := 118140960795 + 678908 * 2 ^ 59
def prefixEnd_678908 : Nat := 4983230072969 + 3 ^ 40 * 678908 * 2
def baseEnd_678908 : Nat := 38734013798081667003085

theorem tailTrace_678908 : CollatzResearch.WordTrace tailWord_678908 prefixEnd_678908 38734013798081667003085 := by
  unfold tailWord_678908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380904512219869550198689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16507872682959826066931585 12380904512219869550198689)
  ·
    refine ⟨9285678384164902162649017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12380904512219869550198689 9285678384164902162649017)
    ·
      refine ⟨6964258788123676621986763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285678384164902162649017 6964258788123676621986763)
      ·
        refine ⟨10446388182185514932980145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964258788123676621986763 10446388182185514932980145)
        ·
          refine ⟨7834791136639136199735109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10446388182185514932980145 7834791136639136199735109)
          ·
            refine ⟨1469023338119838037450333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7834791136639136199735109 1469023338119838037450333)
            ·
              refine ⟨550883751794939264043875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1469023338119838037450333 550883751794939264043875)
              ·
                refine ⟨826325627692408896065813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550883751794939264043875 826325627692408896065813)
                ·
                  refine ⟨38734013798081667003085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 826325627692408896065813 38734013798081667003085)
                  ·
                    rfl

theorem cell23_678908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 6].length) (baseStart_678908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678908 prefixEnd_678908 := by exact prefixLift 678908
  have htrace : WordTrace (prefixWord ++ tailWord_678908) baseStart_678908 baseEnd_678908 := by
    simpa [prefixWord, tailWord_678908, baseEnd_678908] using wordTrace_append hprefix tailTrace_678908
  have hstable : (prefixWord ++ tailWord_678908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678908).length < 2 ^ (prefixWord ++ tailWord_678908).sum := by decide
  have hdescent : baseEnd_678908 < baseStart_678908 := by decide
  rcases family_descends (prefixWord ++ tailWord_678908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678945 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_678945 : Nat := 118140960795 + 678945 * 2 ^ 59
def prefixEnd_678945 : Nat := 4983230072969 + 3 ^ 40 * 678945 * 2
def baseEnd_678945 : Nat := 348625122966951358265095

theorem tailTrace_678945 : CollatzResearch.WordTrace tailWord_678945 prefixEnd_678945 348625122966951358265095 := by
  unfold tailWord_678945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763158525305694419494289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16508772350203796279662859 24763158525305694419494289)
  ·
    refine ⟨18572368893979270814620717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24763158525305694419494289 18572368893979270814620717)
    ·
      refine ⟨6964638335242226555482769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18572368893979270814620717 6964638335242226555482769)
      ·
        refine ⟨5223478751431669916612077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6964638335242226555482769 5223478751431669916612077)
        ·
          refine ⟨1958804531786876218729529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5223478751431669916612077 1958804531786876218729529)
          ·
            refine ⟨1469103398840157164047147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958804531786876218729529 1469103398840157164047147)
            ·
              refine ⟨2203655098260235746070721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469103398840157164047147 2203655098260235746070721)
              ·
                refine ⟨1652741323695176809553041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203655098260235746070721 1652741323695176809553041)
                ·
                  refine ⟨1239555992771382607164781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1652741323695176809553041 1239555992771382607164781)
                  ·
                    refine ⟨464833497289268477686793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1239555992771382607164781 464833497289268477686793)
                    ·
                      refine ⟨348625122966951358265095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464833497289268477686793 348625122966951358265095)
                      ·
                        rfl

theorem cell23_678945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_678945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678945 prefixEnd_678945 := by exact prefixLift 678945
  have htrace : WordTrace (prefixWord ++ tailWord_678945) baseStart_678945 baseEnd_678945 := by
    simpa [prefixWord, tailWord_678945, baseEnd_678945] using wordTrace_append hprefix tailTrace_678945
  have hstable : (prefixWord ++ tailWord_678945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678945).length < 2 ^ (prefixWord ++ tailWord_678945).sum := by decide
  have hdescent : baseEnd_678945 < baseStart_678945 := by decide
  rcases family_descends (prefixWord ++ tailWord_678945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678958 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_678958 : Nat := 118140960795 + 678958 * 2 ^ 59
def prefixEnd_678958 : Nat := 4983230072969 + 3 ^ 40 * 678958 * 2
def baseEnd_678958 : Nat := 348631798215459807402535

theorem tailTrace_678958 : CollatzResearch.WordTrace tailWord_678958 prefixEnd_678958 348631798215459807402535 := by
  unfold tailWord_678958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095454084282324704964691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16509088449505731759811685 3095454084282324704964691)
  ·
    refine ⟨4643181126423487057447037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3095454084282324704964691 4643181126423487057447037)
    ·
      refine ⟨1741192922408807646542639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4643181126423487057447037 1741192922408807646542639)
      ·
        refine ⟨2611789383613211469813959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741192922408807646542639 2611789383613211469813959)
        ·
          refine ⟨3917684075419817204720939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611789383613211469813959 3917684075419817204720939)
          ·
            refine ⟨5876526113129725807081409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917684075419817204720939 5876526113129725807081409)
            ·
              refine ⟨4407394584847294355311057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876526113129725807081409 4407394584847294355311057)
              ·
                refine ⟨3305545938635470766483293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4407394584847294355311057 3305545938635470766483293)
                ·
                  refine ⟨1239579726988301537431235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3305545938635470766483293 1239579726988301537431235)
                  ·
                    refine ⟨1859369590482452306146853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239579726988301537431235 1859369590482452306146853)
                    ·
                      refine ⟨348631798215459807402535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1859369590482452306146853 348631798215459807402535)
                      ·
                        rfl

theorem cell23_678958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_678958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678958 prefixEnd_678958 := by exact prefixLift 678958
  have htrace : WordTrace (prefixWord ++ tailWord_678958) baseStart_678958 baseEnd_678958 := by
    simpa [prefixWord, tailWord_678958, baseEnd_678958] using wordTrace_append hprefix tailTrace_678958
  have hstable : (prefixWord ++ tailWord_678958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678958).length < 2 ^ (prefixWord ++ tailWord_678958).sum := by decide
  have hdescent : baseEnd_678958 < baseStart_678958 := by decide
  rcases family_descends (prefixWord ++ tailWord_678958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678961 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_678961 : Nat := 118140960795 + 678961 * 2 ^ 59
def prefixEnd_678961 : Nat := 4983230072969 + 3 ^ 40 * 678961 * 2
def baseEnd_678961 : Nat := 348633338657423295665021

theorem tailTrace_678961 : CollatzResearch.WordTrace tailWord_678961 prefixEnd_678961 348633338657423295665021 := by
  unfold tailWord_678961
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763742093247729152076737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16509161395498486101384491 24763742093247729152076737)
  ·
    refine ⟨18572806569935796864057553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24763742093247729152076737 18572806569935796864057553)
    ·
      refine ⟨13929604927451847648043165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18572806569935796864057553 13929604927451847648043165)
      ·
        refine ⟨5223601847794442868016187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13929604927451847648043165 5223601847794442868016187)
        ·
          refine ⟨7835402771691664302024281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223601847794442868016187 7835402771691664302024281)
          ·
            refine ⟨5876552078768748226518211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835402771691664302024281 5876552078768748226518211)
            ·
              refine ⟨8814828118153122339777317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876552078768748226518211 8814828118153122339777317)
              ·
                refine ⟨1652780272153710438708247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8814828118153122339777317 1652780272153710438708247)
                ·
                  refine ⟨2479170408230565658062371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652780272153710438708247 2479170408230565658062371)
                  ·
                    refine ⟨3718755612345848487093557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479170408230565658062371 3718755612345848487093557)
                    ·
                      refine ⟨348633338657423295665021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3718755612345848487093557 348633338657423295665021)
                      ·
                        rfl

theorem cell23_678961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_678961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678961 prefixEnd_678961 := by exact prefixLift 678961
  have htrace : WordTrace (prefixWord ++ tailWord_678961) baseStart_678961 baseEnd_678961 := by
    simpa [prefixWord, tailWord_678961, baseEnd_678961] using wordTrace_append hprefix tailTrace_678961
  have hstable : (prefixWord ++ tailWord_678961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678961).length < 2 ^ (prefixWord ++ tailWord_678961).sum := by decide
  have hdescent : baseEnd_678961 < baseStart_678961 := by decide
  rcases family_descends (prefixWord ++ tailWord_678961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_678998 : List Nat := [5, 2, 2, 1, 13]
def baseStart_678998 : Nat := 118140960795 + 678998 * 2 ^ 59
def prefixEnd_678998 : Nat := 4983230072969 + 3 ^ 40 * 678998 * 2
def baseEnd_678998 : Nat := 478261093884279356519

theorem tailTrace_678998 : CollatzResearch.WordTrace tailWord_678998 prefixEnd_678998 478261093884279356519 := by
  unfold tailWord_678998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547818224632105279448353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16510061062742456314115765 1547818224632105279448353)
  ·
    refine ⟨1160863668474078959586265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1547818224632105279448353 1160863668474078959586265)
    ·
      refine ⟨870647751355559219689699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160863668474078959586265 870647751355559219689699)
      ·
        refine ⟨1305971627033338829534549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870647751355559219689699 1305971627033338829534549)
        ·
          refine ⟨478261093884279356519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1305971627033338829534549 478261093884279356519)
          ·
            rfl

theorem cell23_678998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 13].length) (baseStart_678998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_678998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_678998 prefixEnd_678998 := by exact prefixLift 678998
  have htrace : WordTrace (prefixWord ++ tailWord_678998) baseStart_678998 baseEnd_678998 := by
    simpa [prefixWord, tailWord_678998, baseEnd_678998] using wordTrace_append hprefix tailTrace_678998
  have hstable : (prefixWord ++ tailWord_678998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_678998).length < 2 ^ (prefixWord ++ tailWord_678998).sum := by decide
  have hdescent : baseEnd_678998 < baseStart_678998 := by decide
  rcases family_descends (prefixWord ++ tailWord_678998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679009 : List Nat := [1, 2, 3, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_679009 : Nat := 118140960795 + 679009 * 2 ^ 59
def prefixEnd_679009 : Nat := 4983230072969 + 3 ^ 40 * 679009 * 2
def baseEnd_679009 : Nat := 348657985728839107864801

theorem tailTrace_679009 : CollatzResearch.WordTrace tailWord_679009 prefixEnd_679009 348657985728839107864801 := by
  unfold tailWord_679009
  simp only [CollatzResearch.WordTrace]
  refine ⟨24765492797073833349824081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16510328531382555566549387 24765492797073833349824081)
  ·
    refine ⟨18574119597805375012368061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24765492797073833349824081 18574119597805375012368061)
    ·
      refine ⟨6965294849177015629638023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18574119597805375012368061 6965294849177015629638023)
      ·
        refine ⟨10447942273765523444457035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965294849177015629638023 10447942273765523444457035)
        ·
          refine ⟨15671913410648285166685553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10447942273765523444457035 15671913410648285166685553)
          ·
            refine ⟨11753935057986213875014165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15671913410648285166685553 11753935057986213875014165)
            ·
              refine ⟨550965705843103775391289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11753935057986213875014165 550965705843103775391289)
              ·
                refine ⟨413224279382327831543467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550965705843103775391289 413224279382327831543467)
                ·
                  refine ⟨619836419073491747315201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413224279382327831543467 619836419073491747315201)
                  ·
                    refine ⟨464877314305118810486401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619836419073491747315201 464877314305118810486401)
                    ·
                      refine ⟨348657985728839107864801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464877314305118810486401 348657985728839107864801)
                      ·
                        rfl

theorem cell23_679009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_679009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679009 prefixEnd_679009 := by exact prefixLift 679009
  have htrace : WordTrace (prefixWord ++ tailWord_679009) baseStart_679009 baseEnd_679009 := by
    simpa [prefixWord, tailWord_679009, baseEnd_679009] using wordTrace_append hprefix tailTrace_679009
  have hstable : (prefixWord ++ tailWord_679009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679009).length < 2 ^ (prefixWord ++ tailWord_679009).sum := by decide
  have hdescent : baseEnd_679009 < baseStart_679009 := by decide
  rcases family_descends (prefixWord ++ tailWord_679009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679031 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_679031 : Nat := 118140960795 + 679031 * 2 ^ 59
def prefixEnd_679031 : Nat := 4983230072969 + 3 ^ 40 * 679031 * 2
def baseEnd_679031 : Nat := 348669282303238021789699

theorem tailTrace_679031 : CollatzResearch.WordTrace tailWord_679031 prefixEnd_679031 348669282303238021789699 := by
  unfold tailWord_679031
  simp only [CollatzResearch.WordTrace]
  refine ⟨24766295202994131107124947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16510863468662754071416631 24766295202994131107124947)
  ·
    refine ⟨37149442804491196660687421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24766295202994131107124947 37149442804491196660687421)
    ·
      refine ⟨13931041051684198747757783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37149442804491196660687421 13931041051684198747757783)
      ·
        refine ⟨20896561577526298121636675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13931041051684198747757783 20896561577526298121636675)
        ·
          refine ⟨31344842366289447182455013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20896561577526298121636675 31344842366289447182455013)
          ·
            refine ⟨5877157943679271346710315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31344842366289447182455013 5877157943679271346710315)
            ·
              refine ⟨8815736915518907020065473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877157943679271346710315 8815736915518907020065473)
              ·
                refine ⟨6611802686639180265049105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8815736915518907020065473 6611802686639180265049105)
                ·
                  refine ⟨4958852014979385198786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6611802686639180265049105 4958852014979385198786829)
                  ·
                    refine ⟨1859569505617269449545061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4958852014979385198786829 1859569505617269449545061)
                    ·
                      refine ⟨348669282303238021789699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1859569505617269449545061 348669282303238021789699)
                      ·
                        rfl

theorem cell23_679031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_679031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679031 prefixEnd_679031 := by exact prefixLift 679031
  have htrace : WordTrace (prefixWord ++ tailWord_679031) baseStart_679031 baseEnd_679031 := by
    simpa [prefixWord, tailWord_679031, baseEnd_679031] using wordTrace_append hprefix tailTrace_679031
  have hstable : (prefixWord ++ tailWord_679031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679031).length < 2 ^ (prefixWord ++ tailWord_679031).sum := by decide
  have hdescent : baseEnd_679031 < baseStart_679031 := by decide
  rcases family_descends (prefixWord ++ tailWord_679031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679051 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_679051 : Nat := 118140960795 + 679051 * 2 ^ 59
def prefixEnd_679051 : Nat := 4983230072969 + 3 ^ 40 * 679051 * 2
def baseEnd_679051 : Nat := 348679551916327943539607

theorem tailTrace_679051 : CollatzResearch.WordTrace tailWord_679051 prefixEnd_679051 348679551916327943539607 := by
  unfold tailWord_679051
  simp only [CollatzResearch.WordTrace]
  refine ⟨24767024662921674522853007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16511349775281116348568671 24767024662921674522853007)
  ·
    refine ⟨37150536994382511784279511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24767024662921674522853007 37150536994382511784279511)
    ·
      refine ⟨55725805491573767676419267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37150536994382511784279511 55725805491573767676419267)
      ·
        refine ⟨83588708237360651514628901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55725805491573767676419267 83588708237360651514628901)
        ·
          refine ⟨15672882794505122158992919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83588708237360651514628901 15672882794505122158992919)
          ·
            refine ⟨23509324191757683238489379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672882794505122158992919 23509324191757683238489379)
            ·
              refine ⟨35263986287636524857734069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23509324191757683238489379 35263986287636524857734069)
              ·
                refine ⟨3305998714465924205412569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35263986287636524857734069 3305998714465924205412569)
                ·
                  refine ⟨2479499035849443154059427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305998714465924205412569 2479499035849443154059427)
                  ·
                    refine ⟨3719248553774164731089141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479499035849443154059427 3719248553774164731089141)
                    ·
                      refine ⟨348679551916327943539607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3719248553774164731089141 348679551916327943539607)
                      ·
                        rfl

theorem cell23_679051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_679051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679051 prefixEnd_679051 := by exact prefixLift 679051
  have htrace : WordTrace (prefixWord ++ tailWord_679051) baseStart_679051 baseEnd_679051 := by
    simpa [prefixWord, tailWord_679051, baseEnd_679051] using wordTrace_append hprefix tailTrace_679051
  have hstable : (prefixWord ++ tailWord_679051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679051).length < 2 ^ (prefixWord ++ tailWord_679051).sum := by decide
  have hdescent : baseEnd_679051 < baseStart_679051 := by decide
  rcases family_descends (prefixWord ++ tailWord_679051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679058 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_679058 : Nat := 118140960795 + 679058 * 2 ^ 59
def prefixEnd_679058 : Nat := 4983230072969 + 3 ^ 40 * 679058 * 2
def baseEnd_679058 : Nat := 116227715426969805384025

theorem tailTrace_679058 : CollatzResearch.WordTrace tailWord_679058 prefixEnd_679058 116227715426969805384025 := by
  unfold tailWord_679058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6191819993474078679589457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16511519982597543145571885 6191819993474078679589457)
  ·
    refine ⟨4643864995105559009692093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6191819993474078679589457 4643864995105559009692093)
    ·
      refine ⟨1741449373164584628634535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4643864995105559009692093 1741449373164584628634535)
      ·
        refine ⟨2612174059746876942951803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741449373164584628634535 2612174059746876942951803)
        ·
          refine ⟨3918261089620315414427705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612174059746876942951803 3918261089620315414427705)
          ·
            refine ⟨2938695817215236560820779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3918261089620315414427705 2938695817215236560820779)
            ·
              refine ⟨4408043725822854841231169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938695817215236560820779 4408043725822854841231169)
              ·
                refine ⟨3306032794367141130923377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408043725822854841231169 3306032794367141130923377)
                ·
                  refine ⟨2479524595775355848192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306032794367141130923377 2479524595775355848192533)
                  ·
                    refine ⟨116227715426969805384025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2479524595775355848192533 116227715426969805384025)
                    ·
                      rfl

theorem cell23_679058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_679058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679058 prefixEnd_679058 := by exact prefixLift 679058
  have htrace : WordTrace (prefixWord ++ tailWord_679058) baseStart_679058 baseEnd_679058 := by
    simpa [prefixWord, tailWord_679058, baseEnd_679058] using wordTrace_append hprefix tailTrace_679058
  have hstable : (prefixWord ++ tailWord_679058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679058).length < 2 ^ (prefixWord ++ tailWord_679058).sum := by decide
  have hdescent : baseEnd_679058 < baseStart_679058 := by decide
  rcases family_descends (prefixWord ++ tailWord_679058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679111 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_679111 : Nat := 118140960795 + 679111 * 2 ^ 59
def prefixEnd_679111 : Nat := 4983230072969 + 3 ^ 40 * 679111 * 2
def baseEnd_679111 : Nat := 348710360755597708789331

theorem tailTrace_679111 : CollatzResearch.WordTrace tailWord_679111 prefixEnd_679111 348710360755597708789331 := by
  unfold tailWord_679111
  simp only [CollatzResearch.WordTrace]
  refine ⟨24769213042704304770037187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16512808695136203180024791 24769213042704304770037187)
  ·
    refine ⟨37153819564056457155055781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24769213042704304770037187 37153819564056457155055781)
    ·
      refine ⟨6966341168260585716572959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37153819564056457155055781 6966341168260585716572959)
      ·
        refine ⟨10449511752390878574859439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6966341168260585716572959 10449511752390878574859439)
        ·
          refine ⟨15674267628586317862289159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449511752390878574859439 15674267628586317862289159)
          ·
            refine ⟨23511401442879476793433739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15674267628586317862289159 23511401442879476793433739)
            ·
              refine ⟨35267102164319215190150609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23511401442879476793433739 35267102164319215190150609)
              ·
                refine ⟨26450326623239411392612957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35267102164319215190150609 26450326623239411392612957)
                ·
                  refine ⟨9918872483714779272229859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26450326623239411392612957 9918872483714779272229859)
                  ·
                    refine ⟨14878308725572168908344789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9918872483714779272229859 14878308725572168908344789)
                    ·
                      refine ⟨348710360755597708789331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14878308725572168908344789 348710360755597708789331)
                      ·
                        rfl

theorem cell23_679111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_679111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679111 prefixEnd_679111 := by exact prefixLift 679111
  have htrace : WordTrace (prefixWord ++ tailWord_679111) baseStart_679111 baseEnd_679111 := by
    simpa [prefixWord, tailWord_679111, baseEnd_679111] using wordTrace_append hprefix tailTrace_679111
  have hstable : (prefixWord ++ tailWord_679111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679111).length < 2 ^ (prefixWord ++ tailWord_679111).sum := by decide
  have hdescent : baseEnd_679111 < baseStart_679111 := by decide
  rcases family_descends (prefixWord ++ tailWord_679111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679122 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_679122 : Nat := 118140960795 + 679122 * 2 ^ 59
def prefixEnd_679122 : Nat := 4983230072969 + 3 ^ 40 * 679122 * 2
def baseEnd_679122 : Nat := 38746223226977462861309

theorem tailTrace_679122 : CollatzResearch.WordTrace tailWord_679122 prefixEnd_679122 38746223226977462861309 := by
  unfold tailWord_679122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6192403561416113412171905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16513076163776302432458413 6192403561416113412171905)
  ·
    refine ⟨4644302671062085059128929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6192403561416113412171905 4644302671062085059128929)
    ·
      refine ⟨3483227003296563794346697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4644302671062085059128929 3483227003296563794346697)
      ·
        refine ⟨2612420252472422845760023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483227003296563794346697 2612420252472422845760023)
        ·
          refine ⟨3918630378708634268640035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612420252472422845760023 3918630378708634268640035)
          ·
            refine ⟨5877945568062951402960053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918630378708634268640035 5877945568062951402960053)
            ·
              refine ⟨551057397005901694027505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5877945568062951402960053 551057397005901694027505)
              ·
                refine ⟨413293047754426270520629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551057397005901694027505 413293047754426270520629)
                ·
                  refine ⟨38746223226977462861309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413293047754426270520629 38746223226977462861309)
                  ·
                    rfl

theorem cell23_679122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_679122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679122 prefixEnd_679122 := by exact prefixLift 679122
  have htrace : WordTrace (prefixWord ++ tailWord_679122) baseStart_679122 baseEnd_679122 := by
    simpa [prefixWord, tailWord_679122, baseEnd_679122] using wordTrace_append hprefix tailTrace_679122
  have hstable : (prefixWord ++ tailWord_679122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679122).length < 2 ^ (prefixWord ++ tailWord_679122).sum := by decide
  have hdescent : baseEnd_679122 < baseStart_679122 := by decide
  rcases family_descends (prefixWord ++ tailWord_679122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679133 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_679133 : Nat := 118140960795 + 679133 * 2 ^ 59
def prefixEnd_679133 : Nat := 4983230072969 + 3 ^ 40 * 679133 * 2
def baseEnd_679133 : Nat := 348721657329996622714231

theorem tailTrace_679133 : CollatzResearch.WordTrace tailWord_679133 prefixEnd_679133 348721657329996622714231 := by
  unfold tailWord_679133
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770015448624602527338053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16513343632416401684892035 24770015448624602527338053)
  ·
    refine ⟨4644377896617112973875885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24770015448624602527338053 4644377896617112973875885)
    ·
      refine ⟨1741641711231417365203457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4644377896617112973875885 1741641711231417365203457)
      ·
        refine ⟨1306231283423563023902593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741641711231417365203457 1306231283423563023902593)
        ·
          refine ⟨979673462567672267926945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306231283423563023902593 979673462567672267926945)
          ·
            refine ⟨734755096925754200945209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979673462567672267926945 734755096925754200945209)
            ·
              refine ⟨551066322694315650708907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734755096925754200945209 551066322694315650708907)
              ·
                refine ⟨826599484041473476063361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551066322694315650708907 826599484041473476063361)
                ·
                  refine ⟨619949613031105107047521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826599484041473476063361 619949613031105107047521)
                  ·
                    refine ⟨464962209773328830285641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 619949613031105107047521 464962209773328830285641)
                    ·
                      refine ⟨348721657329996622714231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 464962209773328830285641 348721657329996622714231)
                      ·
                        rfl

theorem cell23_679133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_679133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679133 prefixEnd_679133 := by exact prefixLift 679133
  have htrace : WordTrace (prefixWord ++ tailWord_679133) baseStart_679133 baseEnd_679133 := by
    simpa [prefixWord, tailWord_679133, baseEnd_679133] using wordTrace_append hprefix tailTrace_679133
  have hstable : (prefixWord ++ tailWord_679133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679133).length < 2 ^ (prefixWord ++ tailWord_679133).sum := by decide
  have hdescent : baseEnd_679133 < baseStart_679133 := by decide
  rcases family_descends (prefixWord ++ tailWord_679133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679155 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4]
def baseStart_679155 : Nat := 118140960795 + 679155 * 2 ^ 59
def prefixEnd_679155 : Nat := 4983230072969 + 3 ^ 40 * 679155 * 2
def baseEnd_679155 : Nat := 348732953904395536639129

theorem tailTrace_679155 : CollatzResearch.WordTrace tailWord_679155 prefixEnd_679155 348732953904395536639129 := by
  unfold tailWord_679155
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770817854544900284638919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16513878569696600189759279 24770817854544900284638919)
  ·
    refine ⟨37156226781817350426958379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24770817854544900284638919 37156226781817350426958379)
    ·
      refine ⟨55734340172726025640437569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37156226781817350426958379 55734340172726025640437569)
      ·
        refine ⟨41800755129544519230328177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55734340172726025640437569 41800755129544519230328177)
        ·
          refine ⟨31350566347158389422746133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41800755129544519230328177 31350566347158389422746133)
          ·
            refine ⟨1469557797523049504191225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31350566347158389422746133 1469557797523049504191225)
            ·
              refine ⟨1102168348142287128143419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1469557797523049504191225 1102168348142287128143419)
              ·
                refine ⟨1653252522213430692215129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102168348142287128143419 1653252522213430692215129)
                ·
                  refine ⟨1239939391660073019161347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653252522213430692215129 1239939391660073019161347)
                  ·
                    refine ⟨1859909087490109528742021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1239939391660073019161347 1859909087490109528742021)
                    ·
                      refine ⟨348732953904395536639129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1859909087490109528742021 348732953904395536639129)
                      ·
                        rfl

theorem cell23_679155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_679155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679155 prefixEnd_679155 := by exact prefixLift 679155
  have htrace : WordTrace (prefixWord ++ tailWord_679155) baseStart_679155 baseEnd_679155 := by
    simpa [prefixWord, tailWord_679155, baseEnd_679155] using wordTrace_append hprefix tailTrace_679155
  have hstable : (prefixWord ++ tailWord_679155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679155).length < 2 ^ (prefixWord ++ tailWord_679155).sum := by decide
  have hdescent : baseEnd_679155 < baseStart_679155 := by decide
  rcases family_descends (prefixWord ++ tailWord_679155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679229 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 6]
def baseStart_679229 : Nat := 118140960795 + 679229 * 2 ^ 59
def prefixEnd_679229 : Nat := 4983230072969 + 3 ^ 40 * 679229 * 2
def baseEnd_679229 : Nat := 38752327941425360790421

theorem tailTrace_679229 : CollatzResearch.WordTrace tailWord_679229 prefixEnd_679229 38752327941425360790421 := by
  unfold tailWord_679229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773516856276810922832741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16515677904184540615221827 24773516856276810922832741)
  ·
    refine ⟨4645034410551902048031139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24773516856276810922832741 4645034410551902048031139)
    ·
      refine ⟨6967551615827853072046709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645034410551902048031139 6967551615827853072046709)
      ·
        refine ⟨653207963983861225504379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6967551615827853072046709 653207963983861225504379)
        ·
          refine ⟨979811945975791838256569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653207963983861225504379 979811945975791838256569)
          ·
            refine ⟨734858959481843878692427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979811945975791838256569 734858959481843878692427)
            ·
              refine ⟨1102288439222765818038641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734858959481843878692427 1102288439222765818038641)
              ·
                refine ⟨826716329417074363528981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102288439222765818038641 826716329417074363528981)
                ·
                  refine ⟨38752327941425360790421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 826716329417074363528981 38752327941425360790421)
                  ·
                    rfl

theorem cell23_679229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_679229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679229 prefixEnd_679229 := by exact prefixLift 679229
  have htrace : WordTrace (prefixWord ++ tailWord_679229) baseStart_679229 baseEnd_679229 := by
    simpa [prefixWord, tailWord_679229, baseEnd_679229] using wordTrace_append hprefix tailTrace_679229
  have hstable : (prefixWord ++ tailWord_679229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679229).length < 2 ^ (prefixWord ++ tailWord_679229).sum := by decide
  have hdescent : baseEnd_679229 < baseStart_679229 := by decide
  rcases family_descends (prefixWord ++ tailWord_679229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679239 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 1, 1, 3]
def baseStart_679239 : Nat := 118140960795 + 679239 * 2 ^ 59
def prefixEnd_679239 : Nat := 4983230072969 + 3 ^ 40 * 679239 * 2
def baseEnd_679239 : Nat := 348776086279373207988743

theorem tailTrace_679239 : CollatzResearch.WordTrace tailWord_679239 prefixEnd_679239 348776086279373207988743 := by
  unfold tailWord_679239
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773881586240582630696771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16515921057493721753797847 24773881586240582630696771)
  ·
    refine ⟨37160822379360873946045157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24773881586240582630696771 37160822379360873946045157)
    ·
      refine ⟨6967654196130163864883467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37160822379360873946045157 6967654196130163864883467)
      ·
        refine ⟨10451481294195245797325201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967654196130163864883467 10451481294195245797325201)
        ·
          refine ⟨7838610970646434347993901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10451481294195245797325201 7838610970646434347993901)
          ·
            refine ⟨2939479113992412880497713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7838610970646434347993901 2939479113992412880497713)
            ·
              refine ⟨2204609335494309660373285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939479113992412880497713 2204609335494309660373285)
              ·
                refine ⟨413364250405183061319991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2204609335494309660373285 413364250405183061319991)
                ·
                  refine ⟨620046375607774591979987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413364250405183061319991 620046375607774591979987)
                  ·
                    refine ⟨930069563411661887969981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620046375607774591979987 930069563411661887969981)
                    ·
                      refine ⟨348776086279373207988743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930069563411661887969981 348776086279373207988743)
                      ·
                        rfl

theorem cell23_679239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_679239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679239 prefixEnd_679239 := by exact prefixLift 679239
  have htrace : WordTrace (prefixWord ++ tailWord_679239) baseStart_679239 baseEnd_679239 := by
    simpa [prefixWord, tailWord_679239, baseEnd_679239] using wordTrace_append hprefix tailTrace_679239
  have hstable : (prefixWord ++ tailWord_679239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679239).length < 2 ^ (prefixWord ++ tailWord_679239).sum := by decide
  have hdescent : baseEnd_679239 < baseStart_679239 := by decide
  rcases family_descends (prefixWord ++ tailWord_679239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679255 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 1, 6]
def baseStart_679255 : Nat := 118140960795 + 679255 * 2 ^ 59
def prefixEnd_679255 : Nat := 4983230072969 + 3 ^ 40 * 679255 * 2
def baseEnd_679255 : Nat := 116261433989948381796223

theorem tailTrace_679255 : CollatzResearch.WordTrace tailWord_679255 prefixEnd_679255 116261433989948381796223 := by
  unfold tailWord_679255
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774465154182617363279219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16516310102788411575519479 24774465154182617363279219)
  ·
    refine ⟨37161697731273926044918829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24774465154182617363279219 37161697731273926044918829)
    ·
      refine ⟨13935636649227722266844561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37161697731273926044918829 13935636649227722266844561)
      ·
        refine ⟨10451727486920791700133421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13935636649227722266844561 10451727486920791700133421)
        ·
          refine ⟨3919397807595296887550033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10451727486920791700133421 3919397807595296887550033)
          ·
            refine ⟨2939548355696472665662525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3919397807595296887550033 2939548355696472665662525)
            ·
              refine ⟨1102330633386177249623447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2939548355696472665662525 1102330633386177249623447)
              ·
                refine ⟨1653495950079265874435171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102330633386177249623447 1653495950079265874435171)
                ·
                  refine ⟨2480243925118898811652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653495950079265874435171 2480243925118898811652757)
                  ·
                    refine ⟨116261433989948381796223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2480243925118898811652757 116261433989948381796223)
                    ·
                      rfl

theorem cell23_679255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_679255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679255 prefixEnd_679255 := by exact prefixLift 679255
  have htrace : WordTrace (prefixWord ++ tailWord_679255) baseStart_679255 baseEnd_679255 := by
    simpa [prefixWord, tailWord_679255, baseEnd_679255] using wordTrace_append hprefix tailTrace_679255
  have hstable : (prefixWord ++ tailWord_679255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679255).length < 2 ^ (prefixWord ++ tailWord_679255).sum := by decide
  have hdescent : baseEnd_679255 < baseStart_679255 := by decide
  rcases family_descends (prefixWord ++ tailWord_679255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679265 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_679265 : Nat := 118140960795 + 679265 * 2 ^ 59
def prefixEnd_679265 : Nat := 4983230072969 + 3 ^ 40 * 679265 * 2
def baseEnd_679265 : Nat := 348789436776390106263623

theorem tailTrace_679265 : CollatzResearch.WordTrace tailWord_679265 prefixEnd_679265 348789436776390106263623 := by
  unfold tailWord_679265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24774829884146389071143249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16516553256097592714095499 24774829884146389071143249)
  ·
    refine ⟨18581122413109791803357437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24774829884146389071143249 18581122413109791803357437)
    ·
      refine ⟨6967920904916171926259039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18581122413109791803357437 6967920904916171926259039)
      ·
        refine ⟨10451881357374257889388559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967920904916171926259039 10451881357374257889388559)
        ·
          refine ⟨15677822036061386834082839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10451881357374257889388559 15677822036061386834082839)
          ·
            refine ⟨23516733054092080251124259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677822036061386834082839 23516733054092080251124259)
            ·
              refine ⟨35275099581138120376686389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23516733054092080251124259 35275099581138120376686389)
              ·
                refine ⟨3307040585731698785314349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35275099581138120376686389 3307040585731698785314349)
                ·
                  refine ⟨1240140219649387044492881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3307040585731698785314349 1240140219649387044492881)
                  ·
                    refine ⟨930105164737040283369661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240140219649387044492881 930105164737040283369661)
                    ·
                      refine ⟨348789436776390106263623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930105164737040283369661 348789436776390106263623)
                      ·
                        rfl

theorem cell23_679265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_679265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679265 prefixEnd_679265 := by exact prefixLift 679265
  have htrace : WordTrace (prefixWord ++ tailWord_679265) baseStart_679265 baseEnd_679265 := by
    simpa [prefixWord, tailWord_679265, baseEnd_679265] using wordTrace_append hprefix tailTrace_679265
  have hstable : (prefixWord ++ tailWord_679265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679265).length < 2 ^ (prefixWord ++ tailWord_679265).sum := by decide
  have hdescent : baseEnd_679265 < baseStart_679265 := by decide
  rcases family_descends (prefixWord ++ tailWord_679265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679282 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_679282 : Nat := 118140960795 + 679282 * 2 ^ 59
def prefixEnd_679282 : Nat := 4983230072969 + 3 ^ 40 * 679282 * 2
def baseEnd_679282 : Nat := 348798165947516539751045

theorem tailTrace_679282 : CollatzResearch.WordTrace tailWord_679282 prefixEnd_679282 348798165947516539751045 := by
  unfold tailWord_679282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193862481271200243628025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16516966616723200649674733 6193862481271200243628025)
  ·
    refine ⟨4645396860953400182721019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6193862481271200243628025 4645396860953400182721019)
    ·
      refine ⟨6968095291430100274081529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645396860953400182721019 6968095291430100274081529)
      ·
        refine ⟨5226071468572575205561147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6968095291430100274081529 5226071468572575205561147)
        ·
          refine ⟨7839107202858862808341721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226071468572575205561147 7839107202858862808341721)
          ·
            refine ⟨5879330402144147106256291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7839107202858862808341721 5879330402144147106256291)
            ·
              refine ⟨8818995603216220659384437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879330402144147106256291 8818995603216220659384437)
              ·
                refine ⟨826780837801520686817291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8818995603216220659384437 826780837801520686817291)
                ·
                  refine ⟨1240171256702281030225937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826780837801520686817291 1240171256702281030225937)
                  ·
                    refine ⟨930128442526710772669453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240171256702281030225937 930128442526710772669453)
                    ·
                      refine ⟨348798165947516539751045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930128442526710772669453 348798165947516539751045)
                      ·
                        rfl

theorem cell23_679282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_679282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679282 prefixEnd_679282 := by exact prefixLift 679282
  have htrace : WordTrace (prefixWord ++ tailWord_679282) baseStart_679282 baseEnd_679282 := by
    simpa [prefixWord, tailWord_679282, baseEnd_679282] using wordTrace_append hprefix tailTrace_679282
  have hstable : (prefixWord ++ tailWord_679282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679282).length < 2 ^ (prefixWord ++ tailWord_679282).sum := by decide
  have hdescent : baseEnd_679282 < baseStart_679282 := by decide
  rcases family_descends (prefixWord ++ tailWord_679282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679316 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_679316 : Nat := 118140960795 + 679316 * 2 ^ 59
def prefixEnd_679316 : Nat := 4983230072969 + 3 ^ 40 * 679316 * 2
def baseEnd_679316 : Nat := 348815624289769406725889

theorem tailTrace_679316 : CollatzResearch.WordTrace tailWord_679316 prefixEnd_679316 348815624289769406725889 := by
  unfold tailWord_679316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388345003480812390624901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16517793337974416520833201 12388345003480812390624901)
  ·
    refine ⟨2322814688152652323242169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12388345003480812390624901 2322814688152652323242169)
    ·
      refine ⟨1742111016114489242431627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2322814688152652323242169 1742111016114489242431627)
      ·
        refine ⟨2613166524171733863647441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742111016114489242431627 2613166524171733863647441)
        ·
          refine ⟨1959874893128800397735581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613166524171733863647441 1959874893128800397735581)
          ·
            refine ⟨734953084923300149150843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1959874893128800397735581 734953084923300149150843)
            ·
              refine ⟨1102429627384950223726265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734953084923300149150843 1102429627384950223726265)
              ·
                refine ⟨826822220538712667794699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102429627384950223726265 826822220538712667794699)
                ·
                  refine ⟨1240233330808069001692049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826822220538712667794699 1240233330808069001692049)
                  ·
                    refine ⟨930174998106051751269037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1240233330808069001692049 930174998106051751269037)
                    ·
                      refine ⟨348815624289769406725889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 930174998106051751269037 348815624289769406725889)
                      ·
                        rfl

theorem cell23_679316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_679316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679316 prefixEnd_679316 := by exact prefixLift 679316
  have htrace : WordTrace (prefixWord ++ tailWord_679316) baseStart_679316 baseEnd_679316 := by
    simpa [prefixWord, tailWord_679316, baseEnd_679316] using wordTrace_append hprefix tailTrace_679316
  have hstable : (prefixWord ++ tailWord_679316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679316).length < 2 ^ (prefixWord ++ tailWord_679316).sum := by decide
  have hdescent : baseEnd_679316 < baseStart_679316 := by decide
  rcases family_descends (prefixWord ++ tailWord_679316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679345 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_679345 : Nat := 118140960795 + 679345 * 2 ^ 59
def prefixEnd_679345 : Nat := 4983230072969 + 3 ^ 40 * 679345 * 2
def baseEnd_679345 : Nat := 116276838409583264421085

theorem tailTrace_679345 : CollatzResearch.WordTrace tailWord_679345 prefixEnd_679345 116276838409583264421085 := by
  unfold tailWord_679345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24777747723856562734055489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16518498482571041822703659 24777747723856562734055489)
  ·
    refine ⟨18583310792892422050541617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24777747723856562734055489 18583310792892422050541617)
    ·
      refine ⟨13937483094669316537906213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18583310792892422050541617 13937483094669316537906213)
      ·
        refine ⟨2613278080250496850857415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13937483094669316537906213 2613278080250496850857415)
        ·
          refine ⟨3919917120375745276286123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613278080250496850857415 3919917120375745276286123)
          ·
            refine ⟨5879875680563617914429185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919917120375745276286123 5879875680563617914429185)
            ·
              refine ⟨4409906760422713435821889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879875680563617914429185 4409906760422713435821889)
              ·
                refine ⟨3307430070317035076866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409906760422713435821889 3307430070317035076866417)
                ·
                  refine ⟨2480572552737776307649813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307430070317035076866417 2480572552737776307649813)
                  ·
                    refine ⟨116276838409583264421085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2480572552737776307649813 116276838409583264421085)
                    ·
                      rfl

theorem cell23_679345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_679345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679345 prefixEnd_679345 := by exact prefixLift 679345
  have htrace : WordTrace (prefixWord ++ tailWord_679345) baseStart_679345 baseEnd_679345 := by
    simpa [prefixWord, tailWord_679345, baseEnd_679345] using wordTrace_append hprefix tailTrace_679345
  have hstable : (prefixWord ++ tailWord_679345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679345).length < 2 ^ (prefixWord ++ tailWord_679345).sum := by decide
  have hdescent : baseEnd_679345 < baseStart_679345 := by decide
  rcases family_descends (prefixWord ++ tailWord_679345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679455 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_679455 : Nat := 118140960795 + 679455 * 2 ^ 59
def prefixEnd_679455 : Nat := 4983230072969 + 3 ^ 40 * 679455 * 2
def baseEnd_679455 : Nat := 348886998100744362887749

theorem tailTrace_679455 : CollatzResearch.WordTrace tailWord_679455 prefixEnd_679455 348886998100744362887749 := by
  unfold tailWord_679455
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781759753458051520559819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16521173168972034347039879 24781759753458051520559819)
  ·
    refine ⟨37172639630187077280839729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781759753458051520559819 37172639630187077280839729)
    ·
      refine ⟨27879479722640307960629797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37172639630187077280839729 27879479722640307960629797)
      ·
        refine ⟨5227402447995057742618087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27879479722640307960629797 5227402447995057742618087)
        ·
          refine ⟨7841103671992586613927131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227402447995057742618087 7841103671992586613927131)
          ·
            refine ⟨11761655507988879920890697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841103671992586613927131 11761655507988879920890697)
            ·
              refine ⟨8821241630991659940668023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11761655507988879920890697 8821241630991659940668023)
              ·
                refine ⟨13231862446487489911002035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821241630991659940668023 13231862446487489911002035)
                ·
                  refine ⟨19847793669731234866503053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13231862446487489911002035 19847793669731234866503053)
                  ·
                    refine ⟨7442922626149213074938645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19847793669731234866503053 7442922626149213074938645)
                    ·
                      refine ⟨348886998100744362887749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7442922626149213074938645 348886998100744362887749)
                      ·
                        rfl

theorem cell23_679455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_679455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679455 prefixEnd_679455 := by exact prefixLift 679455
  have htrace : WordTrace (prefixWord ++ tailWord_679455) baseStart_679455 baseEnd_679455 := by
    simpa [prefixWord, tailWord_679455, baseEnd_679455] using wordTrace_append hprefix tailTrace_679455
  have hstable : (prefixWord ++ tailWord_679455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679455).length < 2 ^ (prefixWord ++ tailWord_679455).sum := by decide
  have hdescent : baseEnd_679455 < baseStart_679455 := by decide
  rcases family_descends (prefixWord ++ tailWord_679455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679459 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4]
def baseStart_679459 : Nat := 118140960795 + 679459 * 2 ^ 59
def prefixEnd_679459 : Nat := 4983230072969 + 3 ^ 40 * 679459 * 2
def baseEnd_679459 : Nat := 348889052023362347237731

theorem tailTrace_679459 : CollatzResearch.WordTrace tailWord_679459 prefixEnd_679459 348889052023362347237731 := by
  unfold tailWord_679459
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781905645443560203705431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16521270430295706802470287 24781905645443560203705431)
  ·
    refine ⟨37172858468165340305558147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781905645443560203705431 37172858468165340305558147)
    ·
      refine ⟨55759287702248010458337221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37172858468165340305558147 55759287702248010458337221)
      ·
        refine ⟨10454866444171501960938229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55759287702248010458337221 10454866444171501960938229)
        ·
          refine ⟨980143729141078308837959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10454866444171501960938229 980143729141078308837959)
          ·
            refine ⟨1470215593711617463256939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980143729141078308837959 1470215593711617463256939)
            ·
              refine ⟨2205323390567426194885409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470215593711617463256939 2205323390567426194885409)
              ·
                refine ⟨1653992542925569646164057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205323390567426194885409 1653992542925569646164057)
                ·
                  refine ⟨1240494407194177234623043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1653992542925569646164057 1240494407194177234623043)
                  ·
                    refine ⟨1860741610791265851934565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240494407194177234623043 1860741610791265851934565)
                    ·
                      refine ⟨348889052023362347237731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1860741610791265851934565 348889052023362347237731)
                      ·
                        rfl

theorem cell23_679459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_679459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679459 prefixEnd_679459 := by exact prefixLift 679459
  have htrace : WordTrace (prefixWord ++ tailWord_679459) baseStart_679459 baseEnd_679459 := by
    simpa [prefixWord, tailWord_679459, baseEnd_679459] using wordTrace_append hprefix tailTrace_679459
  have hstable : (prefixWord ++ tailWord_679459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679459).length < 2 ^ (prefixWord ++ tailWord_679459).sum := by decide
  have hdescent : baseEnd_679459 < baseStart_679459 := by decide
  rcases family_descends (prefixWord ++ tailWord_679459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679482 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_679482 : Nat := 118140960795 + 679482 * 2 ^ 59
def prefixEnd_679482 : Nat := 4983230072969 + 3 ^ 40 * 679482 * 2
def baseEnd_679482 : Nat := 38766762453157306361125

theorem tailTrace_679482 : CollatzResearch.WordTrace tailWord_679482 prefixEnd_679482 38766762453157306361125 := by
  unfold tailWord_679482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195686131090058782948175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16521829682906823421195133 6195686131090058782948175)
  ·
    refine ⟨9293529196635088174422263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6195686131090058782948175 9293529196635088174422263)
    ·
      refine ⟨13940293794952632261633395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9293529196635088174422263 13940293794952632261633395)
      ·
        refine ⟨20910440692428948392450093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940293794952632261633395 20910440692428948392450093)
        ·
          refine ⟨7841415259660855647168785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20910440692428948392450093 7841415259660855647168785)
          ·
            refine ⟨5881061444745641735376589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7841415259660855647168785 5881061444745641735376589)
            ·
              refine ⟨2205398041779615650766221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5881061444745641735376589 2205398041779615650766221)
              ·
                refine ⟨827024265667355869037333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205398041779615650766221 827024265667355869037333)
                ·
                  refine ⟨38766762453157306361125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 827024265667355869037333 38766762453157306361125)
                  ·
                    rfl

theorem cell23_679482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_679482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679482 prefixEnd_679482 := by exact prefixLift 679482
  have htrace : WordTrace (prefixWord ++ tailWord_679482) baseStart_679482 baseEnd_679482 := by
    simpa [prefixWord, tailWord_679482, baseEnd_679482] using wordTrace_append hprefix tailTrace_679482
  have hstable : (prefixWord ++ tailWord_679482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679482).length < 2 ^ (prefixWord ++ tailWord_679482).sum := by decide
  have hdescent : baseEnd_679482 < baseStart_679482 := by decide
  rcases family_descends (prefixWord ++ tailWord_679482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_679549 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_679549 : Nat := 118140960795 + 679549 * 2 ^ 59
def prefixEnd_679549 : Nat := 4983230072969 + 3 ^ 40 * 679549 * 2
def baseEnd_679549 : Nat := 348935265282266995112317

theorem tailTrace_679549 : CollatzResearch.WordTrace tailWord_679549 prefixEnd_679549 348935265282266995112317 := by
  unfold tailWord_679549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24785188215117505574481701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16523458810078337049654467 24785188215117505574481701)
  ·
    refine ⟨4647222790334532295215319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24785188215117505574481701 4647222790334532295215319)
    ·
      refine ⟨6970834185501798442822979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647222790334532295215319 6970834185501798442822979)
      ·
        refine ⟨10456251278252697664234469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6970834185501798442822979 10456251278252697664234469)
        ·
          refine ⟨1960547114672380812043963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10456251278252697664234469 1960547114672380812043963)
          ·
            refine ⟨2940820672008571218065945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960547114672380812043963 2940820672008571218065945)
            ·
              refine ⟨2205615504006428413549459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940820672008571218065945 2205615504006428413549459)
              ·
                refine ⟨3308423256009642620324189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205615504006428413549459 3308423256009642620324189)
                ·
                  refine ⟨1240658721003615982621571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3308423256009642620324189 1240658721003615982621571)
                  ·
                    refine ⟨1860988081505423973932357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240658721003615982621571 1860988081505423973932357)
                    ·
                      refine ⟨348935265282266995112317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1860988081505423973932357 348935265282266995112317)
                      ·
                        rfl

theorem cell23_679549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_679549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_679549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_679549 prefixEnd_679549 := by exact prefixLift 679549
  have htrace : WordTrace (prefixWord ++ tailWord_679549) baseStart_679549 baseEnd_679549 := by
    simpa [prefixWord, tailWord_679549, baseEnd_679549] using wordTrace_append hprefix tailTrace_679549
  have hstable : (prefixWord ++ tailWord_679549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_679549).length < 2 ^ (prefixWord ++ tailWord_679549).sum := by decide
  have hdescent : baseEnd_679549 < baseStart_679549 := by decide
  rcases family_descends (prefixWord ++ tailWord_679549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
